#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""agda_dedup.py — Agda 库查重 / 语义等价审计的统一入口（单文件，仅标准库）

子命令
  scan   解析 + alpha 形状分组，列出候选（不编译，秒级）
         `--all-types` 另比"非命题型同名 + 定义体逐字相同"（`--prop` 覆盖不到的整类）
  l1     库内语义等价判定：每个候选生成 chkT′ 探针并编译（DEFEQ / NEQ / SCOPE_ERROR / OTHER）
  l2     替换实验：每条人工指定命题生成 audit 探针，证明体换成目标库定理（REPLACED / FAILED）
  cross  与另一个库（默认 agda-stdlib）做 alpha 形状匹配，列出跨库候选（不编译）

判定原理
  L1 探针在被测模块副本尾部追加
      chkT′ : (A) -> (B)
      chkT′ z = z
  z 静态类型是 A 却要对上 B，只有 A 与 B 定义相等才通过；alpha 重命名、隐式/显式 Pi 差异
  由 Agda 自己吸收。判的是「类型相等」，不是「证明体相似」。

边界
  * 只解析顶格声明。**这不是 Agda 的要求**：`module X where` 后接缩进模块体完全合法
    （实测 rc=0），缩进写的探针也能编过（rc=0）。本工具把探针追加在第 1 列，所以只支持
    顶格体；缩进风格的库会大面积漏收，`scan`/`l1` 会打 `note:` 提示。按**命题型**算的覆盖率：
    ALMA 1991/(1991+492)=89%，agda-categories 933/(933+560)=74%（均实测）。
    （旧文案写的 19% 是错口径：分母把 record 字段与 `let`/`where` 绑定也算成"同级声明"，
    真实同级声明只算 `module _` 块体内的那批，见 `indented_stat`。）
  * `--prop` 只决定**候选池**（命题型才进 L1），非命题型（`ℕ → ℕ`、`(v : ℕ) → Fin (n-at v)`
    这类数据/函数定义）整类不进候选——探针也判不了它们（类型本就不 defeq）。这一类由
    `scan --all-types` 用"同名跨文件 + 定义体逐字相同"补，走文本档，不进探针。
  * 探针名用 chkT′ 而不是 chkT：被测模块可能自带 chkT，重名会报 ClashingDefinition
    并被归成 CLASH（假"撞名"）。
  * {- ... -} 块注释先抹成空格再解析（Agda 的 layout 不看注释，注释里的顶格行不是
    布局项）；否则块注释里写一句 `ghost : Set` 就会多出一条幽灵声明。
  * 探针整段复制模块体后追加声明，所以被测模块的模块体必须顶格：`module X where`
    的 layout 块起始列由块内第一个 token 决定，模块体缩进会让追加的 chkT 掉出块，
    整份探针在 parse 阶段就失败（实测是 ParseError，不是 NotInScope）。
  * 一个探针只测一对：Agda 每份文件只报首个错误，多测合并会让后面的全部落 OTHER。
  * 编译 cwd 必须是仓库根并带 -i src，才命中 _build 接口缓存；否则全链重编译。
  * 并行度别拉满，默认 4；冷缓存 8 路会压满机器。
  * 探针目录默认 `<root>/_probe`（仓库内，一轮 l1 会落几十个 `Q_*.agda`）。**把它加进
    `.gitignore`**，别提交；`--probe` 可改到别处（临时目录也行，但 cwd 仍须是仓库根）。
  * L2 只回答「能不能用目标库给出来」，不等于「原库抄了目标库」。
  * 跨文件候选默认不编译，改比类型文本 + 定义体。**理由是探针在此处失效，不是「跨模块
    永不 defeq」**：chkT′ 比的是类型（命题），两个不同模块里的类型当然可以归约到同一
    范式——本仓库就发生过（`u-dyadic-0` 在 Real/Interval/Mul/Order.agda:156，`u-0`/`u-0ℝ`
    在另两个文件，三者 DEFEQ 后由 6c0d44c 合并）。所以「不同常量」讲的是证明项，与
    判据无关，别拿它当跨文件不编译的理由。
    真正的原因：探针把 A 的模块体整段复制再 `open import B`，两套 import 落进同一作用
    域——`using` 列表叠加即 Ambiguous（实测 `_<_` 二义，SCOPE_ERROR），B 与 A 有同名
    声明则更早死在 ClashingDefinition。所以跨文件探针给的是「测不出来」，`--cross-file
    try` 只作反例用。
  * 文本档只回答「文本是否同形」，不回答「语义是否相等」。显式/隐式写法、α 改名、
    中缀 vs 前缀都会让文本不同而命题同一，故 CROSS_NAME 是**待定档**，不是结论。
  * 定义体的边界是「下一个新声明行」，不是「下一个顶格行」——Agda 的证明子句
    （`foo x = ...`、中缀写法 `m +ʳ zero = m`）也顶格，按顶格截断就只剩类型行。
"""

import argparse
import collections
import difflib
import itertools
import json
import os
import re
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

KEY = {'record', 'data', 'module', 'open', 'private', 'variable', 'infix', 'infixl',
       'infixr', 'postulate', 'primitive', 'instance', 'field', 'constructor',
       'pattern', 'macro', 'syntax', 'mutual', 'abstract', 'public', 'where',
       'using', 'hiding', 'renaming', 'let', 'in'}
DECL = re.compile(r'^([^\s]+?)\s*:\s')
TOP = re.compile(r'^(?:record|data|module|pattern|postulate|primitive|instance|field|constructor)\s+([^\s(:]+)')
BIND = re.compile(r'[{(]\s*([^{}()]*?)\s*:')
IDENT = re.compile(r'^[A-Za-z][A-Za-z0-9′₀-₉]*$')
OPTIONS = re.compile(r'\{-#\s*OPTIONS\s+(.*?)#-\}', re.S)

DEFAULT_L2_IMPORTS = '''open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _≤_; _<_; ∣_∣)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; ≤⇒≯
  ; +-assoc; +-identityʳ; +-identityˡ; +-inverseˡ; +-mono-≤; nonNegative⁻¹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥)'''


# ---------------------------------------------------------------- 解析层

def read_lines(path):
    with open(path, encoding='utf-8') as f:
        return f.read().split('\n')


def strip_block_comments(lines):
    """把 {- ... -} 块注释替换成空格，行数不变、行号不动。

    Agda 的 layout 规则不看注释，所以注释里的顶格行**不是**布局项。若不清掉，
    它会被当成真声明：实测 `{- ... ghost : Set ... -}` 这种写法会让解析器多出
    一条 `ghost`，进而进入候选表并被判「重复」。`-- ` 行注释留给 norm_txt 处理，
    `{-# ... #-}` pragma 原样保留（`{-` 后紧跟 `#` 时不进入块注释状态）。

    **必须跟踪字符串字面量**：Agda 里 `"{-"` 只是两个字符，不开注释。若不看引号，
    `msg = "unterminated {- brace"` 会让解析器一直停在注释态，**把该行之后的所有
    声明全部抹掉**，而文件本身 `rc=0` 完全合法——这是静默整段丢失。实测三类库
    （ALMA / stdlib / agda-categories）目前都没有这种写法，但代价太高，必须堵住。
    字符串不跨行（Agda 没有多行字符串），所以 `in_str` 逐行复位。
    """
    out, depth = [], 0
    for l in lines:
        buf, j, in_str = [], 0, False
        while j < len(l):
            c = l[j]
            if in_str:
                buf.append(c)
                if c == '\\' and j + 1 < len(l):
                    buf.append(l[j + 1])
                    j += 2
                    continue
                if c == '"':
                    in_str = False
                j += 1
                continue
            if depth == 0 and c == '"':
                in_str = True
                buf.append(c)
                j += 1
                continue
            if depth == 0 and l.startswith('--', j):
                buf.append(l[j:])
                break
            if l.startswith('{-', j) and not l.startswith('{-#', j):
                depth += 1
                j += 2
                continue
            if depth > 0 and l.startswith('-}', j):
                depth -= 1
                j += 2
                buf.append(' ')
                continue
            if depth > 0:
                j += 1
                continue
            buf.append(c)
            j += 1
        out.append(''.join(buf))
    return out


def read_src(path):
    """读盘并去掉块注释：给解析、record 结构、定义体比对用（探针仍用原样源码）。

    结果缓存在 `_src_cache` 里：全量比对时同一文件会被 478 个候选对反复请求，
    不缓存就变成几千次读盘。调用方只读不写这个 list，共享是安全的。"""
    hit = _src_cache.get(path)
    if hit is None:
        hit = strip_block_comments(read_lines(path))
        _src_cache[path] = hit
    return hit


_src_cache = {}


def module_name(rel):
    return rel[:-5].replace('/', '.')


def parse_module(path, rel):
    """单文件的顶层声明。"""
    return parse_lines(read_src(path), rel)


def parse_file(path, rel):
    """一次读盘：返回 (顶层声明列表, 本模块定义的全部顶层名)。

    名字集合要含 record / data / module / pattern / postulate 声明出的类型构造，
    否则像 RealI 这种不带 `:` 绑定的顶层名会被当成外来词，跨库筛词就失效。
    """
    lines = read_src(path)
    names = set()
    for l in lines:
        if l.strip() and (len(l) - len(l.lstrip()) == 0):
            m = TOP.match(l)
            if m:
                names.add(m.group(1))
    return parse_lines(lines, rel), names


def parse_lines(lines, rel):
    out = []
    i = 0
    while i < len(lines):
        line = lines[i]
        top = bool(line.strip()) and (len(line) - len(line.lstrip()) == 0)
        if top and not line.lstrip().startswith('--') and not line.lstrip().startswith('{-#'):
            m = DECL.match(line)
            if m and m.group(1) not in KEY:
                name = m.group(1)
                # 类型续行一律缩进；任何顶格行（含 private / module / open / pragma）
                # 都是下一个声明或块的边界，必须停下，否则会吞掉后续声明。
                j = i + 1
                while j < len(lines):
                    nxt = lines[j]
                    if bool(nxt.strip()) and (len(nxt) - len(nxt.lstrip()) == 0):
                        break
                    j += 1
                typ = '\n'.join(lines[i:j])
                typ = re.sub(r'^\s*' + re.escape(name) + r'\s*:\s*', '', typ, count=1)
                typ = '\n'.join(x for x in typ.split('\n')
                                if x.strip() and not x.lstrip().startswith('--'))
                typ = re.sub(r'\s+', ' ', typ).strip()
                if typ:
                    out.append(dict(file=rel, name=name, line=i + 1, typ=typ))
                i = max(j, i + 1)
                continue
        i += 1
    return out


def shape(typ):
    """只重命名 Pi 绑定变量，其余原样（运算符、字面量、类型名保留）。"""
    names = set()
    for m in BIND.finditer(typ):
        for n in m.group(1).split():
            if IDENT.match(n):
                names.add(n)
    for n in sorted(names, key=len, reverse=True):
        typ = re.sub(r'(?<![A-Za-z0-9′₀-₉])' + re.escape(n) + r'(?![A-Za-z0-9′₀-₉])', 'v', typ)
    return re.sub(r'\s+', '', typ)


def list_agda_files(root, filters):
    files = []
    for dp, _, fns in os.walk(root):
        for f in fns:
            if f.endswith('.agda'):
                p = os.path.join(dp, f)
                if filters and not any(re.search(x, p) for x in filters):
                    continue
                files.append(p)
    return sorted(files)


def collect(src_dirs, filters, prop_re):
    """返回 (全部顶层声明, 命题型声明, 文件数, 本库定义的全部顶层名集合)。"""
    decls, files, names = [], 0, set()
    for root in src_dirs:
        for p in list_agda_files(root, filters):
            files += 1
            ds, ns = parse_file(p, os.path.relpath(p, root))
            decls += ds
            names |= ns | {d['name'] for d in ds}
    props = [d for d in decls if prop_re.search(d['typ']) and len(d['typ']) > 6]
    return decls, props, files, names


def build_candidates(decls, prop_re):
    """形状分组 + 同名跨文件补充。"""
    by = collections.defaultdict(list)
    for d in decls:
        if prop_re.search(d['typ']) and len(d['typ']) > 6:
            by[shape(d['typ'])].append(d)
    cands, seen = [], set()
    for g in by.values():
        for a, b in itertools.combinations(g, 2):
            if a['name'] != b['name'] or a['file'] != b['file']:
                cands.append((a, b))
                seen.add((a['file'], a['name'], b['file'], b['name']))
    by_name = collections.defaultdict(list)
    for d in decls:
        if prop_re.search(d['typ']) and len(d['typ']) > 6:
            by_name[d['name']].append(d)
    for g in by_name.values():
        for a, b in itertools.combinations(g, 2):
            if a['file'] != b['file'] and (a['file'], a['name'], b['file'], b['name']) not in seen:
                cands.append((a, b))
    return cands


# ---------------------------------------------------------------- 探针层

# `source_text` 的兜底缓存（调用方不给 cache 时用它）。键是 rel，只增不删：
# 一次 run 里的源文件数上界就是仓库文件数，不需要淘汰。
_text_cache = {}


def source_text(rel, src_dirs, cache=None):
    # cache=None 时落到模块级缓存：`options_of` 每造一个 L2 探针都要读一遍源文件，
    # 而它没有调用方的 cache 可用——不兜这一层，同一文件会被重复读 N 次。
    if cache is None:
        cache = _text_cache
    if rel not in cache:
        for root in src_dirs:
            p = os.path.join(root, rel)
            if os.path.isfile(p):
                text = '\n'.join(read_lines(p))
                cache[rel] = text.replace(' --double-check', '').replace('--double-check ', '')
                break
        else:
            raise SystemExit('source not found: %s' % rel)
    return cache[rel]


def options_of(rel, src_dirs):
    m = OPTIONS.search(source_text(rel, src_dirs))
    return '{-# OPTIONS %s #-}' % re.sub(r'\s+', ' ', m.group(1).strip()) if m else ''


def insert_after_module(text, line):
    out = text.split('\n')
    for i, l in enumerate(out):
        if l.startswith('module '):
            out.insert(i + 1, line)
            return '\n'.join(out)
    return line + '\n' + text


def rename_first_module(text, newname):
    return re.sub(r'(?m)^module\s+[^\s]+(\s+)where', 'module ' + newname + r'\1where', text, count=1)


def write_probe(probe_dir, tag, body):
    os.makedirs(probe_dir, exist_ok=True)
    p = os.path.join(probe_dir, 'Q_%s.agda' % tag)
    with open(p, 'w', encoding='utf-8') as f:
        f.write(body)
    return p


def body_diff(ba, bb, span=40, ctx=8):
    """两段定义体第一个不同处：(A 位置, B 位置, A 附近, B 附近)；完全相同返回 None。

    只给前 60 字符对人工复核没用的：`-four-rearrange` 类的长证明前 60 字符往往一样，
    真正分叉的位置在 200 字符开外。用 SequenceMatcher 找首个非 equal 块，再取该位置
    前 8 / 后 40 字符，一眼能看到"从这里开始一个用 sym、一个用 trans"。
    """
    sm = difflib.SequenceMatcher(None, ba, bb, autojunk=False)
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag != 'equal':
            return (i1, j1, ba[max(0, i1 - ctx):i1 + span],
                    bb[max(0, j1 - ctx):j1 + span])
    return None


def probe_l1(task, src_dirs, probe_dir, cache, include=(), skip=()):
    text = source_text(task['a']['file'], src_dirs, cache)
    if task['b']['file'] != task['a']['file']:
        mod = module_name(task['b']['file'])
        if ('open import %s' % mod) not in text and ('import %s' % mod) not in text:
            text = insert_after_module(text, 'open import %s' % mod)
    pname = 'Q_' + task['tag']
    text = rename_first_module(text, pname)
    marker = '-- === AUDIT %s ===' % task['tag']
    text += '\n\n' + marker + '\n'
    # 探针名要在「被测文件自己的声明 ∪ 它 import 链上转出的名字」里唯一。
    # 只查被测文件文本不够：A 自己不写 `chkT′`、但 `open import CH` 把它转出来时，
    # 探针叫 `chkT′` 照样报 Multiple definitions（实测 rc=42、判 CLASH）。
    # 包模块也绕不过去（匿名/具名模块的内层声明同样不许与 import 名重名）。
    taken = visible_names(src_dirs, include, task['a']['file'])
    taken |= visible_names(src_dirs, include, task['b']['file'])
    taken |= set(skip)
    probe_name = 'chkT′'
    for i in range(50):
        n = 'chkT′' + ('' if i == 0 else str(i))
        if n not in taken and n not in text:
            probe_name = n
            break
    task['probe_name'] = probe_name
    text += '%s : (%s) → (%s)\n%s z = z\n' % (probe_name, task['a']['typ'],
                                             task['b']['typ'], probe_name)
    lines = text.split('\n')
    task['marker'] = next(i for i, l in enumerate(lines, 1) if marker in l)
    # marker 在 m 行，声明在 m+1，定义在 m+2；NEQ 的报错落在这两行之一。
    task['probe_line'] = task['marker'] + 2
    return write_probe(probe_dir, task['tag'], text)


IMPORT_LINE = re.compile(r'^(?:open\s+)?import\s+[A-Z]')


def file_imports(path):
    """被测文件自己的顶层 import 块（含 `using (...)` 的续行）。

    只取首行会把多行 `using (` 截断，探针直接 ParseError——所以续行（缩进行）
    必须一起收，直到下一个顶格行为止。
    """
    lines, out, i = read_src(path), [], 0
    while i < len(lines):
        l = lines[i]
        if not IMPORT_LINE.match(l):
            i += 1
            continue
        out.append(l.rstrip())
        i += 1
        while i < len(lines) and (not lines[i].strip() or lines[i][:1] in (' ', '\t')):
            if lines[i].strip():
                out.append(lines[i].rstrip())
            i += 1
    return '\n'.join(out)


def probe_l2(case, src_dirs, probe_dir, default_imports, use_file=False, tag=None):
    path = src_path(src_dirs, case['file'])
    decls = {d['name']: d for d in parse_module(path, case['file'])}
    if case['name'] not in decls:
        # 用 LookupError 而不是 SystemExit：SystemExit 是退出信号，线程池收不住，
        # 一条过期用例（d72d569 就删过 ≤∧<⇒⊥）会把整批 l2 打死、一条结果都不出。
        raise LookupError('decl not found: %s @ %s' % (case['name'], case['file']))
    d = decls[case['name']]
    imports = case.get('imports')
    if not imports:
        # 默认只用 ℚ 模板；只有在模板跑不通（NotInScope/Ambiguous/ParseError）时
        # 才回退到"原文件自己的 import 块"。两者**不能合并**：合并会把
        # `Data.Nat._+_` 和 `Data.Rational._+_` 同时打开，直接 Ambiguous。
        imports = file_imports(path) if use_file else default_imports
    # rhs 写成完全限定名（`Data.Nat.Properties.+-comm`）时，把它的模块补进来。
    # 默认 imports 是 ℚ 模板，其中没有 `Data.Nat.Properties`——不补这一句，
    # 一条 Nat 定理的用例会直接 NotInScope，看起来像"替换失败"，其实只是没导入。
    m = re.match(r'^([A-Z][A-Za-z0-9.\']*)\.([^\s]+)$', case['rhs'].strip())
    if m:
        line = 'open import %s' % m.group(1)
        if line not in imports:
            imports = line + '\n' + imports
    clause = case.get('clause')
    tail = 'audit %s = %s' % (clause, case['rhs']) if clause else 'audit = %s' % case['rhs']
    body = '\n'.join([options_of(case['file'], src_dirs), '',
                      'module Q_%s where' % (tag or case['tag']), '',
                      imports.strip(), '',
                      '-- 原定义：%s:%d' % (case['file'], d['line']),
                      'audit : %s' % d['typ'], tail, ''])
    return write_probe(probe_dir, tag or case['tag'], body)


# ---------------------------------------------------------------- 编译层

def agda_bin(explicit):
    if explicit:
        return explicit
    for c in ('agda', os.path.expanduser('~/.cabal/bin/agda')):
        found = shutil.which(c)
        if found:
            return found
        if os.path.isfile(c):
            return c
    raise SystemExit('agda not found; pass --agda')


def agda_config_dirs():
    """Agda 的配置目录，按优先级返回所有存在的：AGDA_DIR → XDG_CONFIG_HOME/agda → ~/.config/agda。

    Agda 2.8 仍然认 `AGDA_DIR`（实测：`AGDA_DIR=/tmp/agdir2 agda -l std2` 能找到
    `/tmp/agdir2/libraries` 里登记的库，同一命令不设该变量就报 `Library 'std2' not found`）。
    只写死 `~/.config/agda` 会在自定义 AGDA_DIR / XDG 的环境里静默漏掉依赖，
    表现出来是 `default_includes` 少了一项、探针 `NotInScope`——所以三个都扫，去重。
    """
    cands = []
    d = os.environ.get('AGDA_DIR')
    if d:
        cands.append(os.path.expanduser(d))
    x = os.environ.get('XDG_CONFIG_HOME')
    if x:
        cands.append(os.path.join(os.path.expanduser(x), 'agda'))
    cands.append(os.path.expanduser('~/.config/agda'))
    out = []
    for c in cands:
        if os.path.isdir(c) and c not in out:
            out.append(c)
    return out


def default_includes(root=None):
    """自动找 -i 目录：`.agda-lib` 声明的 include，外加配置目录下的 stdlib / categories。

    `.agda-lib` 的 `include:` 是相对仓库根的源目录（可以是多个，也可以不是 `src`），
    不读它就只能假定 `<root>/src`。`depend:` 用来补 `<agda dir>/<name>/src` 的名字。
    配置目录按 `agda_config_dirs()` 的顺序全扫（AGDA_DIR / XDG / 默认）。
    只认这种传统布局；nix / flake / 项目内 vendored 依赖发现不了，要显式传 --include。
    """
    out, deps = [], set()
    if root:
        lib = os.path.join(root, '.agda-lib')
        if os.path.isfile(lib):
            for l in read_lines(lib):
                m = re.match(r'^depend\s*:\s*(.*)$', l)
                if m:
                    deps |= {x.strip() for x in m.group(1).split() if x.strip()}
                m = re.match(r'^include\s*:\s*(.*)$', l)
                if m:
                    for rel in m.group(1).split():
                        p = os.path.join(root, rel)
                        if os.path.isdir(p) and p not in out:
                            out.append(p)
    for base in agda_config_dirs():
        for name in sorted(os.listdir(base)):
            d = os.path.join(base, name, 'src')
            if not os.path.isdir(d):
                continue
            if re.match(r'(agda-stdlib|agda-categories)', name) or name in deps:
                if d not in out:
                    out.append(d)
    return out


def compile_probe(path, ctx):
    cmd = [ctx['agda']]
    if ctx.get('safe'):
        # --safe 禁掉 postulate / NON_TERMINATING 这类信任后门，让「编过」更可信；
        # 代价是被测库若真用了这些，整链会编不过，探针全落 OTHER。所以默认关闭。
        cmd.append('--safe')
    for d in [ctx['probe']] + ctx['src'] + ctx['include']:
        cmd += ['-i', d]
    cmd.append(path)
    r = subprocess.run(cmd, capture_output=True, text=True, cwd=ctx['root'])
    return r.returncode, (r.stdout + r.stderr).strip()


def norm_txt(s):
    """去掉行注释、压缩所有空白，用来判断两处类型文本是否逐字相同。"""
    s = re.sub(r'--.*', '', s)
    return re.sub(r'\s+', '', s)


def src_path(src_dirs, rel):
    """源文件可能来自多个 -i 目录，按相对路径找到真实存在的那份。"""
    for d in src_dirs:
        p = os.path.join(d, rel)
        if os.path.exists(p):
            return p
    return os.path.join(src_dirs[0], rel)


def is_decl_start(l):
    """顶格行是不是"新声明的开头"（而不是上一条声明的证明子句）。

    证明子句有三种写法，都不能当边界：
      * 前缀名：`foo x = ...`
      * 中缀名：`m +ʳ zero = m`、`zero ⊔ n = n`（名字不在行首！）
      * with 块：`foo x with y`、`... | z = ...`
    它们的共同特征是顶格、但不以 `name :` 形态出现。所以判据取"像声明"而不是
    "不像子句"，否则中缀运算符的定义体永远取不到。"""
    if DECL.match(l) or TOP.match(l):
        return True
    if l.startswith('{-#'):
        return True
    if re.match(r'^(open|import)\s', l):
        return True
    # 一行多名（`rot0 rot1 : ...`）与冒号后换行：有冒号、且冒号前没有等号
    return ':' in l and '=' not in l


def decl_body(path, line, name):
    """取一条声明的完整源码块（声明行到下一个新声明行），去注释压空白，
    并把声明名替换成占位符，好让改名后的同一定义也能对上。"""
    ls = read_src(path)
    out = [ls[line - 1]] if line <= len(ls) else []
    for l in ls[line:]:
        if l and not l[0].isspace() and is_decl_start(l):
            break
        out.append(l)
    body = norm_txt('\n'.join(out))
    return body.replace(name, '\x00NAME')


def records_of(path):
    """该文件里每个 record / data 的字段名列表，用来判断同名类型是否同构。"""
    out, lines, i = {}, read_src(path), 0
    while i < len(lines):
        m = TOP.match(lines[i])
        if m and lines[i].startswith(('record', 'data')):
            nm, j, fields = m.group(1), i + 1, []
            while j < len(lines):
                l = lines[j]
                if l and not l[0].isspace():
                    break
                ms = re.match(r'\s+(?:field\s+)?([^\s:{}()]+)\s*:\s', l)
                if ms and not l.lstrip().startswith(('field', 'constructor')):
                    fields.append(ms.group(1))
                j += 1
            out[nm] = fields
            i = j
            continue
        i += 1
    return out


def module_imports(path):
    """该文件直接 import 的模块，换算成本 -i 目录下的相对路径。"""
    out = []
    for l in read_lines(path):
        m = re.match(r'^open import ([\w.]+)|^import ([\w.]+)', l)
        if m:
            out.append((m.group(1) or m.group(2)).replace('.', os.sep) + '.agda')
    return out


_VIS_CACHE = {}
_MOD_CACHE = {}


def _module_view(p, r):
    """(顶层名集合, import 列表)，按 (路径, 相对名) 缓存。

    `visible_names` 从每个候选文件出发走两跳 import，同一模块会被不同起点反复打开。
    实测全仓 244 个文件冷跑 `visible_names` 要 9.96 s（名字累加 194451）、热跑 0 s——
    这 9.96 s 基本全是重复的 `parse_module` + `module_imports`。缓存键的上界就是仓库
    文件数，不需要 LRU 淘汰（峰值内存实测 58 MB，远没到需要管的地步）。
    """
    k = (p, r)
    v = _MOD_CACHE.get(k)
    if v is None:
        v = (frozenset(x['name'] for x in parse_module(p, r)), tuple(module_imports(p)))
        _MOD_CACHE[k] = v
    return v


def _find_rel(src_dirs, include, rel):
    for d in list(src_dirs) + list(include or ()):
        p = os.path.join(d, rel)
        if os.path.exists(p):
            return p
    return None


def visible_names(src_dirs, include, rel, depth=2):
    """`rel` 里能直接引用的顶层名：自己声明的 + 沿 import 链转出的（depth 跳）。

    探针名落在这个集合里就会撞，而**包模块没用**——实测 `module _ where` 与
    `module AuditProbe_x where` 里的同名声明一样报 `[ClashingDefinition]
    Multiple definitions of chkT′`（Agda 不允许在内层作用域重定义已 import 的名字）。
    所以只能让探针名在整个可见命名空间里唯一。depth 2 足够覆盖 stdlib 的两跳
    re-export；再深的 public 链极罕见，真撞了 CLASH 档会显式报出来，不会静默。
    """
    key = (tuple(src_dirs), tuple(include or ()), rel, depth)
    if key in _VIS_CACHE:
        return _VIS_CACHE[key]
    names, seen = set(), set()

    def walk(r, d):
        if r in seen or d < 0:
            return
        seen.add(r)
        p = _find_rel(src_dirs, include, r)
        if not p:
            return
        mnames, mimps = _module_view(p, r)
        names.update(mnames)
        if d:
            for imp in mimps:
                walk(imp, d - 1)

    walk(rel, depth)
    _VIS_CACHE[key] = names
    return names


def find_record(src_dirs, rel, name, depth=4, seen=None):
    """找 name 这个 record/data 的真实定义位置：先本文件，再沿 import 追 depth 跳。

    depth 由 2 提到 4：stdlib 的 `Data.Rational` → `.Base` → `…` 这类 re-export 链
    经常超过两跳，追不到就返回 None，而 None 在 `shape_conflicts` 里等于「不比了」，
    会把「没查到」伪装成「没有结构冲突」。多读几个文件走的是 `_src_cache`，几乎不花钱。
    """
    seen = set() if seen is None else seen
    if depth < 0 or rel in seen:
        return None
    seen.add(rel)
    path = src_path(src_dirs, rel)
    if not os.path.exists(path):
        return None
    got = records_of(path).get(name)
    if got is not None:
        return (rel, got)
    if depth == 0:
        return None
    for imp in module_imports(path):
        r = find_record(src_dirs, imp, name, depth - 1, seen)
        if r:
            return r
    return None


def name_forms(n):
    """`_+_` 在表达式里写成 `+`，`_≤_` 写成 `≤`：中缀名的两种形态都要能对上。"""
    forms = {n}
    for inner in re.findall(r'_([^_]+)_', n):
        if inner:
            forms.add(inner)
    return forms


IMPORT_USE = re.compile(
    r"open\s+import\s+([A-Za-z0-9.'’]+)"
    r'(?:\s+as\s+\S+)?'
    r'((?:\s+(?:using|renaming)\s*\([^)]*\))+)')

_CLAUSE = re.compile(r'(using|renaming)\s*\(([^)]*)\)')

# Agda 的导入列表三种分隔都见过：`;`（ALMA 全库）、`,`、纯空白（stdlib 常见）。
# 空白分隔时一项里会挤很多名字（`using (ℕ zero suc _+_ _*_)`），必须逐 token 收。
_CLAUSE_SPLIT = re.compile(r'[;,|]')


def _clause_names(raw, rename):
    """括号内的**本地**名。

    `x as y`（using）与 `a to b`（renaming）都取右侧——左侧是外部名，
    本文件里根本不叫这个名字，收进来只会污染映射。
    """
    out = []
    kw = 'to' if rename else 'as'
    for chunk in _CLAUSE_SPLIT.split(raw):
        toks = chunk.split()
        if not toks:
            continue
        if kw in toks:
            i = toks.index(kw)
            if i + 1 < len(toks):
                out.append(toks[i + 1])
            continue
        out.extend(toks)
    return out


def _renaming_pairs(raw):
    pairs = {}
    for chunk in _CLAUSE_SPLIT.split(raw):
        toks = chunk.split()
        if 'to' in toks:
            i = toks.index('to')
            if i > 0 and i + 1 < len(toks):
                pairs[toks[i - 1]] = toks[i + 1]
    return pairs


def import_forms(path, src_dirs=None):
    """本文件 `open import M using (...)` / `renaming (...)` 建立的 form → 模块 映射。

    显式列表能逐一列出名字；`open import M public` 不能——但 public 确实会把名字
    倒进本文件作用域。旧版直接跳过 public，于是「一侧 public 拿到 `+`、另一侧
    `using` 拿到 `+`」这种情况里 public 侧查不到映射，`CROSS_SCOPE` 静默漏判。
    现在给了 `src_dirs` 就沿 public 链解析出**真正声明该名字的模块**
    （`_mod_origins`），这样 `Prelude public` 转出的 `+` 也会归到 `Data.Nat.Base`，
    不会跟对侧的 `Data.Nat.Base` 误判成两个来源。

    先 `using` 选名字，再按 `renaming` 改名——本地能引用的只有改名后的那个。
    所以 `using (a) renaming (a to b)` 记的是 `b`，`a` 不记。
    显式导入优先于 public（`setdefault` 在 public 之后）。
    """
    out = {}
    src = ' '.join(read_src(path))
    for m in IMPORT_USE.finditer(src):
        mod, clauses = m.group(1), m.group(2)
        names, ren = [], []
        for kind, raw in _CLAUSE.findall(clauses):
            if kind == 'using':
                names.extend(_clause_names(raw, False))
            else:
                ren.extend(_clause_names(raw, True))
        alias = {}
        for kind, raw in _CLAUSE.findall(clauses):
            if kind == 'renaming':
                alias.update(_renaming_pairs(raw))
        names = [alias.get(n, n) for n in names] if names else ren
        for n in names:
            if not n or n in ('module', '...'):
                continue
            for f in name_forms(n):
                out[f] = mod
    if src_dirs:
        for l in read_src(path):
            m = PUBLIC_USE.match(l)
            if not m:
                continue
            for f, origin in _mod_origins(src_dirs, m.group(1)).items():
                out.setdefault(f, origin)
    return out


PUBLIC_USE = re.compile(r"^open\s+import\s+([A-Za-z0-9.'’]+)\b.*\bpublic\b")


def _mod_origins(src_dirs, mod, depth=3, seen=None):
    """模块对外可见的 form → **真正声明它的模块**，沿 `public` 链传递。

    本模块自己声明的名字归自己（`setdefault` 之前先填），只有自己没声明的才沿用
    更深一层 public 的来源。这样 `Prelude public` 里的 `_+_` 仍然记作
    `Data.Nat.Base`，`_mod_root` 才有机会把它和对侧的 `Data.Nat.Base` 认成同一个。
    """
    rel = mod.replace('.', '/') + '.agda'
    path = src_path(src_dirs, rel)
    if not os.path.exists(path):
        return {}
    seen = set() if seen is None else seen
    if path in seen:
        return {}
    seen.add(path)
    decls, names = parse_file(path, rel)
    out = {}
    for n in set(names) | {d['name'] for d in decls}:
        for f in name_forms(n):
            out.setdefault(f, mod)
    if depth:
        for l in read_src(path):
            m = PUBLIC_USE.match(l)
            if not m or m.group(1) == mod:
                continue
            for f, origin in _mod_origins(src_dirs, m.group(1), depth - 1, seen).items():
                out.setdefault(f, origin)
    return out


def _occurs(form, typ):
    return re.search(r'(?<![A-Za-z0-9_\'₀-₉])' + re.escape(form) +
                     r'(?![A-Za-z0-9_\'₀-₉])', typ) is not None


BASE_NAMES = {'≡', 'refl', 'cong', 'sym', 'trans', 'subst', 'ℕ', 'ℤ', 'ℚ', 'ℝ',
              '⊤', '⊥', 'Bool', 'true', 'false', 'tt', 'suc', 'zero',
              'Set', 'Level', 'String', 'Char', 'ℕ∞', '⊎', '×', 'Σ'}


def _mod_root(m):
    """`Data.Nat` 与 `Data.Nat.Base` 是同一个 `ℕ` 的两条 re-export 路径，不是两个来源。"""
    return '.'.join(m.split('.')[:2])


def scope_conflicts(path_a, typ_a, path_b, typ_b, src_dirs=None):
    """类型文本逐字相同，但同一个符号在两个文件里来自不同模块 → 量化域不同。

    这是 `shape_conflicts` 覆盖不到的一层：后者只看同名 record/data 的字段表，
    而 `+interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)` 这种
    **完全靠隐式推断**的类型里根本没有类型标注——一侧的 `+` 是 ℚ 加法
    （`Data.Rational`），另一侧是 ℕ 加法（`Data.Nat.Base`），字面一模一样，
    却是两个不同命题。

    两道校准，避免把「同一常量的两条 re-export 路径」误判成冲突：
      * 模块名前两段相同即视同（`Data.Nat` ↔ `Data.Nat.Base`）；
      * `≡`/`ℕ`/`refl` 这类基础名不可能有第二份实现，直接跳过。
    """
    ma, mb = import_forms(path_a, src_dirs), import_forms(path_b, src_dirs)
    rows = []
    for f, mod_a in ma.items():
        mod_b = mb.get(f)
        if mod_b is None or mod_b == mod_a:
            continue
        if f in BASE_NAMES or _mod_root(mod_a) == _mod_root(mod_b):
            continue
        if _occurs(f, typ_a) and _occurs(f, typ_b):
            rows.append('%s: %s vs %s' % (f, mod_a, mod_b))
    return rows


_TOKEN = re.compile(r'[A-Za-z_][A-Za-z0-9′₀-₉_]*')


def _carrier_reach(path, typ, rec):
    """`rec` 这个 record 名是否与被比的类型有关：直接出现，或出现于该类型里某个符号
    的声明类型。

    只查「类型文本里有没有 `Obs`」会漏掉真正的情况——`bracket-self : ∀ f → bracket f f
    ≡ zero` 的文本里根本没有 `Obs`，`Obs` 是 `bracket` 的参数类型。所以再看一层：
    类型里出现过的符号，各自在本文件声明时用的类型是否提到这个 record
    （`bracket : Obs → Obs → Obs` 一眼命中）。本仓 8 条全部靠这一层命中。
    """
    forms = name_forms(rec)
    if any(_occurs(f, typ) for f in forms):
        return True
    decls = {d['name']: d['typ'] for d in parse_module(path, '')}
    for tok in set(_TOKEN.findall(typ)):
        d = decls.get(tok)
        if d and any(_occurs(f, d) for f in forms):
            return True
    return False


def shape_conflicts(src_dirs, fa, ta, fb, tb):
    """两处同名声明若建立在结构不同的 record 上，就不是同一命题。

    类型里最容易被隐式推断掉的那一层正是数据类型：`Poisson` 与 `Quadratic*`
    各有一个 `Obs`（3 字段 vs 6 字段），而类型文本都写着 `∀ f → bracket f f ≡ zero`。
    只比字面会把这种「同形不同义」判成复制品。

    前置条件（不加会把无关记录也拖进来）：这个 record 名必须和两条类型有关系，
    判据见 `_carrier_reach`。否则甲文件声明 `Ctx`、乙文件声明另一个同名 `Ctx` 时，
    两边所有文本相同的引理都会被判 CROSS_SHAPE——那已经不是证据，是巧合。
    """
    rows, unresolved = [], []
    pa, pb = src_path(src_dirs, fa), src_path(src_dirs, fb)
    for nm in sorted(set(records_of(pa)) | set(records_of(pb))):
        if not (_carrier_reach(pa, ta, nm) or _carrier_reach(pb, tb, nm)):
            continue
        A = find_record(src_dirs, fa, nm)
        B = find_record(src_dirs, fb, nm)
        if A and B and A[1] != B[1]:
            rows.append('%s: %s(%d 字段) vs %s(%d 字段)'
                        % (nm, A[0], len(A[1]), B[0], len(B[1])))
        elif not A or not B:
            # 追 import 没找到。不能当成「无冲突」——那会把漏判伪装成通过。
            unresolved.append('%s(A=%s, B=%s)' % (nm, 'ok' if A else 'miss',
                                                 'ok' if B else 'miss'))
    return rows, unresolved


ERROR_HEAD = re.compile(r'^.*?:\d+\.\d+-\d+: error:.*$', re.M)


def brief_error(out, limit=400):
    """取**第一条** `file:line.col-col: error:` 起的 limit 字符，而不是末尾 limit 字符。

    末尾截断的问题是：`.agda` 里错误按声明顺序报，模块体自己的错会挂在 chkT 的错
    后面；而 `when checking` 展开可能得很长，把真正的 `!=` 挤到 400 字符之外。
    末尾只有在找不到标准 error 行时才当兜底。
    """
    m = ERROR_HEAD.search(out)
    if m:
        return out[m.start():m.start() + limit].strip()
    return out[-limit:].strip()


ERR_TAG = re.compile(r':\s*\[([A-Za-z][A-Za-z0-9]*)\]')


def error_tag(out):
    """取首个 `[Tag]`（`[NotInScope]` / `[SafeFlagPostulate]` / `[UnequalSorts]` …）。

    `OTHER` / `FAILED` 是黑箱：同一个桶里混着"探针本身不合法"（SafeFlagPostulate）、
    "类型不匹配但不是定义不等"（UnequalSorts）、"元变量没解"（UnsolvedMetaVariables）。
    不细分就只能人工翻 stderr，所以把首条错误的标签单独记下来——status 口径不变。
    """
    m = ERR_TAG.search(out)
    return m.group(1) if m else ''


def probe_err_lines(out, pname):
    """探针文件里所有 `Q_x.agda:行.` 的行号。"""
    return [int(m.group(1)) for m in
            re.finditer(r'%s:(\d+)\.' % re.escape(pname + '.agda'), out)]


def classify_l1(rc, out, pname, probe_line):
    if rc == 0:
        return 'DEFEQ'
    # 跨文件候选会把 B 的同名声明 import 进来，与 A 模块体里的同名定义冲突。
    # 这种报错行号落在模块体内部，必然 ≤ probe_line，若不先截住会全部误判 NEQ。
    if 'ClashingDefinition' in out:
        return 'CLASH'
    if 'NotInScope' in out or 'Ambiguous' in out:
        return 'SCOPE_ERROR'
    errs = probe_err_lines(out, pname)
    # 双条件：错误要落在探针那两行上（行号 ≤ probe_line），且必须是定义不等那一类报错文本。
    # probe_line = marker + 2：marker 占一行、类型声明占一行、定义体占一行（**行内追加**，
    # 不包模块——包 `module _ where` 或具名模块都会被 import 名撞，已实测否掉）。
    # 只看行号会被模块体自己的错误吃掉（历史实测：35 条「NEQ」里 25 条其实是 ClashingDefinition）。
    if errs and min(errs) <= probe_line and ('!=' in out or 'does not reduce to' in out):
        return 'NEQ'
    return 'OTHER'


def classify_l2(rc, out):
    if rc == 0:
        return 'REPLACED'
    for key in ('ParseError', 'NotInScope', 'InfectiveImport', 'UnsolvedMetaVariables',
                'NoParseForApplication', 'WrongNamedArgument', 'TypeError'):
        if key in out:
            return key
    return 'FAILED'


# ---------------------------------------------------------------- 子命令

INDENT_DECL = re.compile(r'^\s+[^\s]+?\s*:\s')


def mod_block_ranges(lines):
    """产出 (块头行下标, 块体列, 块结束行下标)：`module _` 块的骨架。

    块体列不能用「`where` 之后第一条语句的缩进」定。首条语句若落在 `private` /
    `abstract` 里（`    L = o ⊔ h ⊔ e ⊔ s ⊔ p` 这种块内局部缩写），列会算成 4，
    而真正的同级引理在列 2——整块被判成 0 条。实测 `SecondPass/Lambek.agda` L46 起的
    块就是这样：L48 起是注释，接着 `    L = …`，而 L199 的 `out∘in≈Fid` 在列 2。
    改成取「块内所有非空非注释行的最小缩进」，`private` 只是块内一层壳，不影响同级列。
    """
    n = len(lines)
    i = 0
    while i < n:
        if not re.match(r'^module\s+_(\s|$)', lines[i]):
            i += 1
            continue
        h = i
        while h < n and not lines[h].rstrip().endswith('where'):
            h += 1
        end = h + 1
        while end < n:
            s = lines[end]
            if s.strip() and (len(s) - len(s.lstrip())) == 0:
                break
            end += 1
        col = None
        for s in lines[h + 1:end]:
            if s.strip() and not s.lstrip().startswith('--'):
                ind = len(s) - len(s.lstrip())
                if col is None or ind < col:
                    col = ind
        yield h, col, end
        i = max(end, i + 1)


def indented_stat(src_dirs, filters, prop_re):
    """统计 `module _` 块体里、与块体同级的引理——这些才是真正的漏收。

    判据：缩进恰等于块体列、以 `name :` 开头、且该行不含 `=`（`=` 说明已经是定义体那一
    行而不是签名）；`(` / `{` 开头的是多行块头的续行，不算声明。返回 (总数, 命题型数)。

    实测 ALMA：旧口径 1391 条（把 `Real/Interval/MonotoneConvergence.agda` L66–71 的
    多行块头续行全算成声明），本口径 492 条（命题型 152）。agda-categories 旧口径
    1268 条，本口径 560 条（命题型 69）。

    判不判得了另说：`module _` 里的声明**是导出的**（实测 `open import … using
    (range-f0)` 能编过，Agda 把块参数折进类型），但源码里写的类型只有半截——块参数在
    块头上、还可能引用块内 private 定义（`{X = CS}` 里的 `CS`）。所以这批既不是
    "收不到"，也不是 "收了就能判"。
    """
    total = prop = 0
    for root in src_dirs:
        for p in list_agda_files(root, filters):
            lines = read_src(p)
            for h, col, end in mod_block_ranges(lines):
                if col is None:
                    continue
                for k in range(h + 1, end):
                    s = lines[k]
                    if not s.strip() or (len(s) - len(s.lstrip())) != col:
                        continue
                    b = s.lstrip()
                    if b.startswith(('--', '(', '{')):
                        continue
                    mt = DECL.match(b)
                    # 不额外要求 `'=' not in b`：`DECL` 已经要求 `name :` 形态，定义体那一行
                    # 本来就不匹配；而签名里的 `{X = CS}` `{o = o}` 这类隐式记录赋值含 `=`，
                    # 按它过滤会把 `counit` 这类正常引理整条丢掉（实测差 14 条 / 8 条命题型）。
                    if mt and ':' in s:
                        total += 1
                        if re.search(prop_re, s.split(':', 1)[1]):
                            prop += 1
    return total, prop


def block_decls(src_dirs, filters):
    """收 `module _` 块体内、与块体同级的声明（口径与 `indented_stat` 完全一致）。

    刻意不并进 `parse_file`：这批的 `typ` 是**半截**的（`∀ y → US._≈U_ {X = CS}
    (out (in-F y)) y` 里的 `CS` 是块内 private 定义、块参数在块头上），拿它跟顶格声明
    的类型做文本配对会造出大量假候选。所以它们自成一批，单独记 `block` 归属。
    """
    out = []
    for root in src_dirs:
        for p in list_agda_files(root, filters):
            rel = os.path.relpath(p, root)
            lines = read_src(p)
            for h, col, end in mod_block_ranges(lines):
                if col is None:
                    continue
                for k in range(h + 1, end):
                    s = lines[k]
                    if not s.strip() or (len(s) - len(s.lstrip())) != col:
                        continue
                    b = s.lstrip()
                    if b.startswith(('--', '(', '{')):
                        continue
                    mt = DECL.match(b)
                    if mt and mt.group(1) not in KEY and ':' in s:
                        out.append(dict(file=rel, name=mt.group(1), line=k + 1,
                                        typ=s.split(':', 1)[1].strip(),
                                        block='%s:%d' % (rel, h + 1)))
    return out


def note_coverage(ind, top, top_prop=None):
    """`module _` 体内还有一批同级引理没纳入时提示一句。

    分母只用同级的口径（顶格 + module _ 体内），不掺字段和 let 绑定。覆盖率按**命题型**
    算——候选本来就按 `--prop` 筛，拿全部声明当分母会把数字压得没意义。
    """
    total, prop = ind
    if not total or total <= top * 0.1:
        return
    pct = 100.0 * (top_prop or top) / ((top_prop or top) + prop)
    print('note: `module _` 体内另有 %d 条同级声明（其中命题型 %d；顶格 %d / '
          '命题型 %d，按命题型覆盖 %.0f%%）。这些是导出的，但源码里的类型只有半截'
          '（块参数在块头上，还可能引用块内 private 定义），判不了等价——只走文本档 '
          'CROSS_COPY / CROSS_TYPE，不进探针。'
          % (total, prop, top, top_prop or top, pct))


def block_pairs(bds, src_dirs, prop_re):
    """`module _` 体内声明的文本档配对：只认「类型文本归一后完全相同」。

    不按 shape 配是刻意的：这些 `typ` 缺块参数，`foo : A → A` 在任意两个块里归一后都
    一样，按 shape 配会造出一大片假候选（实测 ALMA 上 shape 配对只有 1 对，但那是这次
    唯一真像的一对；放宽到 shape 就得靠人一条条看）。文本完全相同至少保证字面是同一句
    话，剩下的只是「符号来自哪个块/哪个文件」——那正是 CROSS_SCOPE 该管的事。
    """
    by = collections.defaultdict(list)
    for d in bds:
        if prop_re.search(d['typ']) and len(d['typ']) > 6:
            by[norm_txt(d['typ'])].append(d)
    out = []
    for g in by.values():
        for a, b in itertools.combinations(g, 2):
            if a['block'] == b['block']:
                continue
            ba = decl_body(src_path(src_dirs, a['file']), a['line'], a['name'])
            bb = decl_body(src_path(src_dirs, b['file']), b['line'], b['name'])
            out.append((a, b, ba == bb))
    return out


def same_name_copies(decls, prop_re, src_dirs):
    """非命题型里「同名 + 定义体逐字相同」的跨文件重复（`scan --all-types`）。

    `--prop` 把数据/函数定义整类挡在候选池外：`n-at : ℕ → ℕ`、`natToFin : (v : ℕ) →
    Fin (n-at v)` 这种类型过不了 `prop_re`，探针也判不了（两个类型本来就不 defeq）。
    所以这一类唯一的证据是**定义体本身**，只能走文本档：
      同名 → 跨文件 → 归一化定义体逐字相同 → CROSS_COPY。
    实测 ALMA（HEAD d72d569）：非命题型 744 条、同名跨文件 36 组、体逐字相同 9 对。
    这一档不进探针，也不该进：`chkT′` 比的是类型，不是函数值。
    """
    nonprop = [d for d in decls if not (prop_re.search(d['typ']) and len(d['typ']) > 6)]
    by = collections.defaultdict(list)
    for d in nonprop:
        by[d['name']].append(d)
    cross = {k: v for k, v in by.items() if len({x['file'] for x in v}) > 1}
    rows = []
    for name, g in sorted(cross.items()):
        for a, b in itertools.combinations(g, 2):
            if a['file'] == b['file']:
                continue
            ba = decl_body(src_path(src_dirs, a['file']), a['line'], name)
            bb = decl_body(src_path(src_dirs, b['file']), b['line'], name)
            if ba and ba == bb:
                rows.append((a, b))
    return len(nonprop), len(cross), rows


def cmd_scan(args, ctx):
    decls, props, files, _ = collect(ctx['src'], args.filter, ctx['prop'])
    cands = build_candidates(decls, ctx['prop'])
    groups = {shape(a['typ']) for a, _ in cands}
    print('files %d  decls %d  prop-typed %d  pairs %d  shape-groups %d'
          % (files, len(decls), len(props), len(cands), len(groups)))
    ind = indented_stat(ctx['src'], args.filter, ctx['prop'])
    note_coverage(ind, len(decls), len(props))
    bds = block_decls(ctx['src'], args.filter)
    bpr = block_pairs(bds, ctx['src'], ctx['prop'])
    print('blocks %d 条同级声明（命题型 %d），类型文本完全相同的配对 %d'
          % (len(bds), sum(1 for d in bds if ctx['prop'].search(d['typ'])), len(bpr)))
    for a, b, same in bpr[:args.show]:
        print('  [块] %s @ %s:%d  <->  %s @ %s:%d  %s'
              % (a['name'], a['file'], a['line'], b['name'], b['file'], b['line'],
                 '类型与定义体都相同' if same else '类型相同、定义体不同'))
    for k, (a, b) in enumerate(cands[:args.show], 1):
        print('  [%d] %s @ %s:%d  <->  %s @ %s:%d'
              % (k, a['name'], a['file'], a['line'], b['name'], b['file'], b['line']))
        print('      A: %s' % a['typ'][:150])
        print('      B: %s' % b['typ'][:150])
    copies = []
    if args.all_types:
        # `--prop` 之外的整类（数据/函数定义）进不了候选池，探针也判不了；
        # 这里用"同名 + 定义体逐字相同"补上，只出文本证据，不进编译。
        n_non, n_cross, copies = same_name_copies(decls, ctx['prop'], ctx['src'])
        print('all-types 非命题型 %d 条，同名跨文件组 %d，定义体逐字相同 %d'
              % (n_non, n_cross, len(copies)))
        for a, b in copies[:args.show]:
            print('  [copy] %s @ %s:%d  <->  %s:%d'
                  % (a['name'], a['file'], a['line'], b['file'], b['line']))
        if copies:
            print('  ⚠ 这一档只说明定义体逐字相同（纯副本）；同一函数的不同写法看不出，'
                  '也别拿它当"可以删"的唯一依据——先看调用点。')
    report = dict(command='scan', files=files, decls=len(decls), props=len(props),
                  pairs=len(cands), groups=len(groups),
                  indented=ind[0], indented_prop=ind[1],
                  all_types=len(copies))
    return report, [dict(a=x, b=y) for x, y in cands]


L1_STATUS_ORDER = ('DEFEQ', 'NEQ', 'CLASH', 'SCOPE_ERROR', 'OTHER',
                   'CROSS_COPY', 'CROSS_TYPE', 'CROSS_SHAPE', 'CROSS_SCOPE', 'CROSS_NAME')

# 结论档与待定档分开打。CROSS_* 全部来自文本比对：它们只说明「文本层面像/不像」，
# 没有一条经过 Agda 的类型检查，不能和 DEFEQ/NEQ 并排当结论读。
L1_DECIDED = ('DEFEQ', 'NEQ', 'CLASH', 'SCOPE_ERROR', 'OTHER')
L1_PENDING = ('CROSS_COPY', 'CROSS_TYPE', 'CROSS_SHAPE', 'CROSS_SCOPE', 'CROSS_NAME')


def cmd_l1(args, ctx):
    decls, props, files, _ = collect(ctx['src'], args.filter, ctx['prop'])
    cands = build_candidates(decls, ctx['prop'])
    if args.max_cases:
        cands = cands[:args.max_cases]
    tasks, used = [], set()
    for a, b in cands:
        tag = re.sub(r'[^A-Za-z0-9]', 'u', a['name'] + '_' + b['name'])[:28]
        k = 1
        while tag in used:
            tag = tag[:24] + str(k)
            k += 1
        used.add(tag)
        tasks.append(dict(tag=tag, a=a, b=b, same=a['file'] == b['file']))
    # `module _` 体内的声明：**不进探针**（typ 缺块参数，探针写不出来），只进文本档。
    # 它们按「类型文本完全相同」配对，档位落 CROSS_COPY / CROSS_TYPE，跟跨文件那批
    # 同档同义，所以并进 count 与待定横幅，不新造 status 名。
    bds = block_decls(ctx['src'], args.filter)
    bpr = block_pairs(bds, ctx['src'], ctx['prop'])
    for a, b, same_body in bpr:
        tag = re.sub(r'[^A-Za-z0-9]', 'u', a['name'] + '_' + b['name'])[:28]
        k = 1
        while tag in used:
            tag = tag[:24] + str(k)
            k += 1
        used.add(tag)
        tasks.append(dict(
            tag=tag, a=a, b=b, same=True, scope='block',
            status='CROSS_COPY' if same_body else 'CROSS_TYPE',
            err=('匿名模块内：类型文本与定义体都逐字相同（纯复制品）' if same_body else
                 '匿名模块内：类型文本相同、定义体不同（同一命题两套证明）')))
    cache = {}
    todo = []
    for t in tasks:
        if t.get('status'):
            continue
        if not t['same'] and args.cross_file == 'skip':
            # 跨文件候选不编译，是因为**探针在这里测不出东西**，不是「跨模块不可能 defeq」：
            # 探针把 A 的模块体整段复制后 `open import B`，两套 import 进同一作用域，
            # `using` 叠加即 Ambiguous（实测 `_<_` 二义 → SCOPE_ERROR），B 与 A 有同名声明
            # 则直接 ClashingDefinition。跨模块的类型本身完全可以转换（本仓库 u-dyadic-0 /
            # u-0 / u-0ℝ 就是三个文件里的同一命题，6c0d44c 合并过），只是这份探针拿不到。
            # 于是改比类型文本与整段定义体。注意这五档**都只是文本证据**，没有一条经过
            # 类型检查，所以 CROSS_NAME 是待定档，不是「不是重复」的结论：
            #   CROSS_NAME   类型文本不同                     → 可能同义（隐式/显式、α、中缀差异），待定
            #   CROSS_SHAPE  同名 record/data 字段表不同     → 同一句话搭在不同对象上，平行实现
            #   CROSS_SCOPE  符号来自不同模块（量化域不同）   → 字面相同、命题不同（ℚ vs ℕ）
            #   CROSS_TYPE   类型相同、证法不同               → 同一命题两套证明，算冗余
            #   CROSS_COPY   类型与定义体都逐字相同           → 纯复制品，可合并/改 re-export
            ta, tb = norm_txt(t['a']['typ']), norm_txt(t['b']['typ'])
            t['typ_same'] = ta == tb
            if not t['typ_same']:
                t['status'] = 'CROSS_NAME'
                t['err'] = '类型文本不同，语义未判定（需探针或人工复核）'
            else:
                pa, pb = (src_path(ctx['src'], t['a']['file']),
                          src_path(ctx['src'], t['b']['file']))
                ba = decl_body(pa, t['a']['line'], t['a']['name'])
                bb = decl_body(pb, t['b']['line'], t['b']['name'])
                t['body_same'] = ba == bb
                # 块是否逐字相同还不够：类型里的数据类型若在两边结构不同（字段数不等），
                # 那就是同一句话搭在不同对象上，是平行实现而不是副本。这条证据比
                # "证法是否相同"更硬（同名 record 字段表是确定的），所以先判。
                sc, shapeless = shape_conflicts(ctx['src'], t['a']['file'], t['a']['typ'],
                                                t['b']['file'], t['b']['typ'])
                t['shape_conflict'] = sc
                t['shape_unresolved'] = shapeless
                # 再看符号来源：类型文本没有类型标注时（`∀ a b c d → (a + b) …`），
                # 同一个 `+` 可能一边是 ℚ 加法、一边是 ℕ 加法，字面完全相同。
                zc = (scope_conflicts(pa, t['a']['typ'], pb, t['b']['typ'], ctx['src'])
                      if not sc else [])
                t['scope_conflict'] = zc
                if sc:
                    t['status'] = 'CROSS_SHAPE'
                    t['err'] = '同名类型结构不同：' + '; '.join(sc)
                elif zc:
                    t['status'] = 'CROSS_SCOPE'
                    t['err'] = '类型文本相同，但符号来源不同：' + '; '.join(zc)
                elif ba != bb:
                    t['status'] = 'CROSS_TYPE'
                    # 类型一样、证法不同：人工复核要看的是两段证明从哪儿开始分叉。
                    # 先给各自前 60 字符定位整段，再给首个差异位置与附近切片。
                    bd = body_diff(ba, bb)
                    t['err'] = ('类型相同但定义体不同：同一命题的两套证明'
                                '  A: %s | B: %s' % (ba[:60], bb[:60]))
                    if bd:
                        i1, j1, acut, bcut = bd
                        t['err'] += ('  首差 A@%d「%s」 | B@%d「%s」'
                                     % (i1, acut, j1, bcut))
                else:
                    t['status'] = 'CROSS_COPY'
                    t['err'] = '类型与定义体均逐字相同：纯复制品'
        else:
            todo.append(t)
    paths = [probe_l1(t, ctx['src'], ctx['probe'], cache, ctx['include']) for t in todo]

    def work(item):
        t, p = item
        rc, out = compile_probe(p, ctx)
        t['status'] = classify_l1(rc, out, 'Q_' + t['tag'], t['probe_line'])
        t['err'] = brief_error(out)
        # visible_names 只走 depth 2，属于「大概率不撞」而非「保证不撞」。真撞了不能把
        # 一对等价声明判成 CLASH：ClashingDefinition 的报错行落在探针行上（≥ marker）
        # 说明是**探针名**被 import 名占了，不是 A/B 两文件真同名（后者报在模块体里）。
        # 这种情况换名重编，最多三次；三次还撞才保留 CLASH。
        pname = 'Q_' + t['tag']
        skip = {t['probe_name']}
        tries = 0
        while (t['status'] == 'CLASH' and tries < 3
               and probe_err_lines(out, pname)
               and min(probe_err_lines(out, pname)) >= t['marker']):
            tries += 1
            p = probe_l1(t, ctx['src'], ctx['probe'], cache, ctx['include'], skip)
            skip.add(t['probe_name'])
            rc, out = compile_probe(p, ctx)
            t['status'] = classify_l1(rc, out, pname, t['probe_line'])
            t['err'] = brief_error(out)
            t['probe_retry'] = tries
        if t['status'] == 'OTHER':
            t['other_tag'] = error_tag(out)
        return t['status']

    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        list(ex.map(work, zip(todo, paths)))
    counts = collections.Counter(t['status'] for t in tasks)
    print('files %d  props %d  pairs %d  ->  %s' % (files, len(props), len(tasks), dict(counts)))
    # 未分类失败的分布：CI 日志里只看 dict(counts) 看不出"为什么失败"，
    # 这一行把它压成 {标签: 条数}，`[SafeFlagPostulate]` 一类能一眼认出来。
    tags = collections.Counter(t.get('other_tag') for t in tasks
                               if t['status'] == 'OTHER' and t.get('other_tag'))
    if tags:
        print('OTHER 错误分布: %s' % dict(tags))
        if 'SafeFlagPostulate' in tags:
            print('  提示: 该库有 postulate/TrustMe，`--safe` 下探针不合法；去掉 --safe 才能判。')
        if 'UnsolvedMetaVariables' in tags:
            print('  提示: 源文件自己有未解元变量，探针会连带失败；这类对结论只能人工看。')
    ind = indented_stat(ctx['src'], args.filter, ctx['prop'])
    note_coverage(ind, len(decls), len(props))
    pending_banner = False
    for st in L1_STATUS_ORDER + tuple(sorted(s for s in counts if s not in L1_STATUS_ORDER)):
        sel = [t for t in tasks if t['status'] == st]
        if not sel:
            continue
        if st in L1_PENDING and not pending_banner:
            # CROSS_* 全来自文本比对，没有一条过过类型检查。在这里切一刀，免得
            # 读者把下面几档和上面的 DEFEQ/NEQ 当成同一等级的证据。
            # 注意 banner 必须挂"第一个**有内容的**待定档"上：CROSS_COPY/CROSS_TYPE
            # 经常是 0 条，挂死在 CROSS_COPY 上会让整条分隔线静默消失。
            pending_banner = True
            print('\n' + '=' * 60)
            print('以下为文本档（未编译、未过类型检查）：只说明文本是否同形，'
                  '不说明命题是否等价')
            print('=' * 60)
        print('\n### %s (%d)' % (st, len(sel)))
        for t in sel:
            print('  %s @ %s:%d  <->  %s @ %s:%d  [%s]'
                  % (t['a']['name'], t['a']['file'], t['a']['line'],
                     t['b']['name'], t['b']['file'], t['b']['line'], t['tag']))
            print('    A: %s' % t['a']['typ'][:140])
            print('    B: %s' % t['b']['typ'][:140])
            # DEFEQ/NEQ 的 err 是整段编译输出，太长；其余档一律打，新加档位也不会漏。
            if st not in ('DEFEQ', 'NEQ'):
                print('    err: %s' % t['err'].replace('\n', ' | ')[-160:])
            if t.get('other_tag'):
                # OTHER 是混桶：探针自身不合法（SafeFlagPostulate）、类型不等但不是
                # 定义不等（UnequalSorts）、元变量未解（UnsolvedMetaVariables）都在这儿。
                # 至少把首条错误的标签打出来，省掉人工翻 stderr。
                print('    ⚠ 未分类错误标签: [%s]' % t['other_tag'])
            if t.get('shape_unresolved'):
                # 追 import 没追到同名 record 时，`shape_conflicts` 无法比对；
                # 这不能当成"没有结构冲突"，必须显出来。
                print('    ⚠ record 未解析（本档可能不准）: %s' % '; '.join(t['shape_unresolved']))
    report = dict(command='l1', files=files, decls=len(decls), props=len(props),
                  pairs=len(tasks), counts=dict(counts), probe=ctx['probe'],
                  indented=ind[0], indented_prop=ind[1])
    cases = [{k: t.get(k) for k in ('tag', 'same', 'status', 'err', 'typ_same', 'body_same',
                                   'shape_conflict', 'shape_unresolved', 'scope_conflict',
                                   'other_tag', 'probe_name', 'probe_retry')}
             | dict(a=t['a'], b=t['b']) for t in tasks]
    return report, cases


def cmd_l2(args, ctx):
    # 用例文件读不到是"参数问题"，不是"被测库有问题"，别让它以裸 traceback 收场。
    try:
        with open(args.cases, encoding='utf-8') as f:
            cases = json.load(f)
    except FileNotFoundError:
        sys.stderr.write('✗ 用例文件不存在：%s\n'
                         '  换成实际存在的路径（仓库自带样例是 l2_cases_example.json）。\n'
                         % args.cases)
        raise SystemExit(2)
    except json.JSONDecodeError as e:
        sys.stderr.write('✗ 用例文件不是合法 JSON：%s（%s）\n' % (args.cases, e))
        raise SystemExit(2)
    if args.max_cases:
        cases = cases[:args.max_cases]
    default_imports = args.imports.replace('\\n', '\n') if args.imports else DEFAULT_L2_IMPORTS
    # 造探针阶段就可能失败（用例里的声明已被删/改名）。逐条收：坏用例记 NOT_FOUND，
    # 其余照跑——口径与 `probe_err_lines` 那句"一条用例的坏数据不该改整批的口径"一致。
    paths = []
    for c in cases:
        try:
            paths.append(probe_l2(c, ctx['src'], ctx['probe'], default_imports))
        except LookupError as e:
            c['status'] = 'NOT_FOUND'
            c['err'] = str(e)
            paths.append(None)

    def work(item):
        c, p = item
        if p is None:
            return 'NOT_FOUND'
        rc, out = compile_probe(p, ctx)
        st = classify_l2(rc, out)
        # 作用域类失败（不是"证不出来"，是"名字没进视野"）时，用原文件自己的
        # import 块重试一次。非 ℚ 的用例（Nat / Stream / 自建 prelude）全靠这条。
        if st in ('NotInScope', 'Ambiguous', 'ParseError') and not c.get('imports'):
            try:
                p2 = probe_l2(c, ctx['src'], ctx['probe'], default_imports,
                              use_file=True, tag=c['tag'] + '_f')
            except LookupError:
                # 声明在这一步才消失是不可能的（前面已经查过一次），只是防御：
                # 真发生就保留模板档的结论，不要让重试把整批带崩。
                p2 = None
            if p2 is not None:
                rc2, out2 = compile_probe(p2, ctx)
                st2 = classify_l2(rc2, out2)
                if st2 != st:
                    c['status'] = st2
                    c['err'] = brief_error(out2)
                    c['probe_variant'] = 'file-imports'
                    return st2
        c['status'] = st
        c['err'] = brief_error(out)
        c['probe_variant'] = 'template'
        if st == 'FAILED':
            c['other_tag'] = error_tag(out)
        return st

    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        statuses = list(ex.map(work, zip(cases, paths)))
    counts = collections.Counter(statuses)
    print('cases %d  ->  %s' % (len(cases), dict(counts)))
    for c in cases:
        print('\n### %s  [%s]  %s:%s' % (c['tag'], c['status'], c['file'], c['name']))
        print('    rhs: %s' % c['rhs'][:150])
        if c['status'] != 'REPLACED':
            print('    err: %s' % c['err'].replace('\n', ' | ')[-180:])
        if c.get('other_tag'):
            print('    ⚠ 未分类错误标签: [%s]' % c['other_tag'])
    return dict(command='l2', cases=len(cases), counts=dict(counts), probe=ctx['probe']), cases


def find_stdlib(root=None):
    for d in default_includes(root):
        if 'stdlib' in d:
            return d
    return None


def cmd_cross(args, ctx):
    other_root = args.other or find_stdlib(ctx['root'])
    if not other_root:
        raise SystemExit('target library not found; pass --other <src-dir>')
    _, mine, _, vocab = collect(ctx['src'], args.filter, ctx['prop'])
    _, theirs, _, _ = collect([other_root], [], ctx['prop'])
    shared = []
    for d in mine:
        # 只要类型里出现任何一个库内自定义顶层名，就不算"纯共享词汇"：
        # 它描述的是本库特有对象，跨库形状匹配必然错配（历史那次 _≈ℝ_ vs _*ℝ_ 假候选）。
        toks = set(re.findall(r'[A-Za-z_][A-Za-z0-9′₀-₉_]*', d['typ']))
        if toks & vocab:
            continue
        if args.drop_qualified and re.search(r'[A-Za-z][A-Za-z0-9]*\.[A-Za-z]', d['typ']):
            continue
        shared.append(d)
    their_by_shape = collections.defaultdict(list)
    for d in theirs:
        their_by_shape[shape(d['typ'])].append(d)
    all_hits = [(d, e) for d in shared for e in their_by_shape.get(shape(d['typ']), [])]
    # 形状命中的数量必须和"体也逐字相同"的数量**一起报**。`shape()` 只把 Pi 绑定名
    # 统一成 `v`，在默认 --prop 口径下对任何二元运算的骨架都成立——实测 ALMA 上
    # 336 条纯共享词汇只剩 1 条命中，而那一条是 `≈-trans` ↔ RingSolver 的 `_⊙_`。
    # 只打一个 `hits` 数会被读成"重复数"，所以两个数一起算，只有 --body 时才过滤。
    body_same = []
    for d, e in all_hits:
        pa = src_path(ctx['src'], d['file'])
        pb = src_path([other_root], e['file'])
        if decl_body(pa, d['line'], d['name']) == decl_body(pb, e['line'], e['name']):
            body_same.append((d, e))
    # 形状匹配只说明"签名骨架一致"，对 `ℕ → ℕ → ℕ` 这种签名毫无区分力
    # （实测 --prop='.*' 时 478 对类型相同里全被误配）。加上定义体逐字比对，
    # 才能回答"是不是把标准库的实现抄了一遍"。
    hits = body_same if args.body else all_hits
    print('mine prop-typed %d  pure-shared-vocab %d  target prop-typed %d  '
          'shape hits %d  其中定义体逐字相同 %d'
          % (len(mine), len(shared), len(theirs), len(all_hits), len(body_same)))
    if not args.body and all_hits and not body_same:
        print('  ⚠ 形状命中的体一条都不相同：这一档只说明"签名骨架像"，'
              '不能当重复数；查真副本请加 --body。')
    for d, e in hits[:args.show]:
        print('  %s @ %s:%d  <->  %s @ %s' % (d['name'], d['file'], d['line'], e['name'], e['file']))
    report = dict(command='cross', mine=len(mine), shared=len(shared),
                  target=len(theirs), hits=len(hits), shape_hits=len(all_hits),
                  body_same=len(body_same), target_root=other_root,
                  body=bool(args.body))
    return report, [dict(a=x, b=y) for x, y in hits]


# ---------------------------------------------------------------- 入口

def add_common(p):
    p.add_argument('--root', help='仓库根（agda 的 cwd，命中接口缓存）；默认 --src 的父目录')
    p.add_argument('--src', action='append', help='源目录，可重复；默认 <root>/src')
    p.add_argument('--include', action='append', default=[],
                   help='额外 -i 目录；默认自动发现 ~/.config/agda 下 stdlib/categories')
    p.add_argument('--probe', help='探针目录；默认 <root>/_probe（仓库内，记得 gitignore）')
    p.add_argument('--agda', help='agda 可执行；默认 PATH 上的 agda，否则 ~/.cabal/bin/agda')
    p.add_argument('--jobs', type=int, default=4, help='并行编译数；默认 4')
    p.add_argument('--out', help='结果 JSON 路径')
    p.add_argument('--filter', action='append', default=[], help='只处理路径匹配该正则的文件')
    p.add_argument('--prop', default=r'(≡|≤|<|≈|#)', help='命题型判据正则')
    p.add_argument('--show', type=int, default=20, help='人读输出最多列几条')
    p.add_argument('--max-cases', type=int, help='只跑前 N 个候选')
    p.add_argument('--safe', action='store_true',
                   help='编译探针时加 --safe（禁 postulate / 非终止标记）；'
                        '被测库若依赖这些会整链失败，默认不开')


def repo_root_of(path):
    """沿祖先目录找带 `.agda-lib` 的那一层（Agda 仓库根的标准判据），找不到返回 None。

    用途：`--root .` 在 `src/` 里给时，默认源目录会被拼成 `src/src`。与其让用户自己
    回退一级，不如沿 `.agda-lib` 找到真正的仓库根——但修正必须打出来，静默修正会让
    "根找错"藏进结果数字里。
    """
    d = os.path.abspath(path)
    while True:
        if os.path.isfile(os.path.join(d, '.agda-lib')):
            return d
        parent = os.path.dirname(d)
        if parent == d:
            return None
        d = parent


def main(argv=None):
    ap = argparse.ArgumentParser(
        prog='agda_dedup.py', description='Agda 查重 / 语义等价审计（scan / l1 / l2 / cross）',
        formatter_class=argparse.RawDescriptionHelpFormatter, epilog=__doc__)
    sub = ap.add_subparsers(dest='cmd', required=True)
    for name, text in (('scan', '解析 + 形状分组，列出候选（不编译）'),
                       ('l1', '库内 L1 判定：chkT 探针 + 编译'),
                       ('l2', '替换实验：audit 探针 + 编译'),
                       ('cross', '跨库形状匹配（不编译）')):
        sp = sub.add_parser(name, help=text)
        add_common(sp)
        if name == 'l1':
            sp.add_argument('--cross-file', choices=('skip', 'try'), default='skip',
                            help='跨文件候选怎么处理：skip 走文本比对（默认；文本档只判'
                                 '"同形"，CROSS_NAME 是待定档）。try 仍搭探针，但探针把 A '
                                 '的模块体复制后再 import B，两套作用域叠加——实测会退成 '
                                 'SCOPE_ERROR（_<_ 二义）或 CLASH，基本测不出东西，只作反例用')
        if name == 'scan':
            sp.add_argument('--all-types', action='store_true',
                            help='补一档文本比对：非命题型（数据/函数定义，探针判不了）里'
                                 '"同名跨文件 + 定义体逐字相同"的纯副本。不进编译，秒级')
        if name == 'l2':
            sp.add_argument('--cases', required=True, help='用例 JSON（见 使用说明.md）')
            sp.add_argument('--imports', help='覆盖默认 import 块，用 \\n 分行')
        if name == 'cross':
            sp.add_argument('--other', help='目标库 src 目录；默认自动找 agda-stdlib')
            sp.add_argument('--drop-qualified', action='store_true',
                            help='丢掉类型里出现限定访问 X.y 的条目（字段泄漏）')
            sp.add_argument('--body', action='store_true',
                            help='形状对上后再比整段定义体，只留"类型与体都逐字相同"的'
                                 '（跨库真副本）。不加时也照样计算并打印"体逐字相同"的条数，'
                                 '只是不过滤——因为形状档几乎没有区分力'
                                 '（实测 ALMA 336 条纯共享词汇只剩 1 条，且是假命中）')
    args = ap.parse_args(argv)
    # 并行度不是越大越好，也不是按 cpu_count 自适应：Agda 编译是内存主导，
    # 实测 7 GB 机器冷缓存 8 路 load 13、机器压满（`ls` 都排不上）。默认 4 是刻意值。
    if getattr(args, 'jobs', 4) > 4:
        sys.stderr.write('⚠ --jobs %d 超过 4：冷缓存下每路 Agda 编译都很吃内存，'
                         '实测 8 路会把机器压满，建议 ≤4\n' % args.jobs)

    src = args.src or [os.path.join(args.root or '.', 'src')]
    root = os.path.abspath(args.root or os.path.dirname(os.path.abspath(src[0])))
    # 只对"没显式给 --src"的情形做上溯修正：给了 --src 就尊重那个目录，错了让它报。
    if not args.src and not os.path.isdir(os.path.join(root, 'src')):
        up = repo_root_of(root)
        if up and up != root and os.path.isdir(os.path.join(up, 'src')):
            sys.stderr.write('note: --root %s 下没有 src/，已沿 .agda-lib 上溯到 %s\n'
                             % (root, up))
            root = up
            src = [os.path.join(root, 'src')]
    # 探针目录默认落在**仓库内**（`<root>/_probe`）。早期默认 `<root>/../audit/probe_dedup`
    # 会把几十份 `Q_*.agda` 写到 clone 外面：别人 clone 到 ~/tools/x，就在 ~/tools/audit/
    # 落一堆文件；两个仓库共用那一层还会互相覆盖。放仓库内 + 提醒 gitignore 更省事。
    probe = args.probe or os.path.join(root, '_probe')
    # 工具自己的副本落在被测源目录里（`src/agda_dedup.py`）是个陷阱：改完主副本、
    # 忘了同步这份，跑起来的是老代码——同样的现象会重复出现两次（一次报错、一次正常）。
    # 只做提示，不改路径：把工具挪到哪是使用者的选择。
    me = os.path.abspath(__file__)
    for s in src:
        if me.startswith(os.path.abspath(s) + os.sep):
            sys.stderr.write('note: 正在运行的是源目录内的副本 %s；改过工具记得把它同步，'
                             '否则跑的是旧版\n' % me)
            break
    ctx = dict(root=root, src=[os.path.abspath(s) for s in src],
               include=args.include or default_includes(root),
               probe=os.path.abspath(probe),
               agda=agda_bin(args.agda), prop=re.compile(args.prop), safe=args.safe)
    # 静默 0 是这套工具最会骗人的输出：`--root` 指错（典型是在 `src/` 里写了 `--root .`，
    # 于是默认源目录被拼成 `<cwd>/src` → `src/src`）时，四条命令都照样打 `files 0`、rc=0。
    # 这里拦成硬错误，并把实际解析出的 root / src 回显出来。
    missing = [s for s in ctx['src'] if not os.path.isdir(s)]
    if missing:
        sys.stderr.write('✗ 源目录不存在：%s\n' % ', '.join(missing))
        sys.stderr.write('  --root 解析为 %s\n' % root)
        sys.stderr.write('  提示：--root 要给**仓库根**，不是 src/。在仓库根里跑 `--root .`，'
                         '或在任意目录写 `--root /path/to/repo`；脚本本身放在哪不影响。\n')
        return 2
    fn = dict(scan=cmd_scan, l1=cmd_l1, l2=cmd_l2, cross=cmd_cross)[args.cmd]
    t0 = time.time()
    report, cases = fn(args, ctx)
    # 计时落在 report 里而不是只打印：CI 要对比"这次比上次慢了多少"时，
    # 日志会被截断/混排，只有 JSON 里的数字是稳定可读的。取一位小数足够
    # （scan 全仓 0.65–0.72 s，毫秒级抖动没有比较意义）。
    elapsed = round(time.time() - t0, 2)
    report['elapsed'] = elapsed
    report['root'] = ctx['root']
    if args.out:
        with open(args.out, 'w', encoding='utf-8') as f:
            json.dump(dict(report=report, cases=cases), f, ensure_ascii=False, indent=1)
        print('\njson -> %s' % args.out)
    print('耗时 %.2f s' % elapsed)
    return 0


if __name__ == '__main__':
    sys.exit(main())
