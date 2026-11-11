# agda_dedup.py 使用说明

单文件工具，四个子命令，把 ALMA 查重审计里三个一次性脚本（`audit_sem_l1.py`、
`l2_replace_probe.py`、以及跨库形状扫描）收进同一个入口。只有标准库依赖，不需要 pip。

```
work/agda_dedup.py          工具本体（489 行）
work/l2_cases_example.json  L2 用例示例（4 条已实证可替换）
```

---

## 1. 四个子命令怎么选

| 子命令 | 干什么 | 要编译吗 | 实测耗时（ALMA 244 文件） | 什么时候用 |
|---|---|---|---|---|
| `scan` | 解析 + α 形状分组，列候选 | 否 | 1–2 秒 | 每轮改库后先跑，看有没有新候选 |
| `l1` | 库内语义等价判定（`chkT′` 探针 + `CROSS_*` 文本比对） | 是（仅同文件） | 9 对 ≈ 40 秒；34 对 ≈ 1 分钟（25 条跨文件不编译） | 候选要靠 Agda 判「定义相不相等」 |
| `l2` | 替换实验（`audit` 探针） | 是 | 4 条 ≈ 50 秒（2 路） | 判断某条能否换成标准库现成定理 |
| `cross` | 与 stdlib 做形状匹配 | 否 | 30–60 秒（要解析 9000+ 声明） | 怀疑与外部库重复时 |

一句话分工：**`scan` 提候选，`l1` 判真假，`l2` 验可替换，`cross` 查外库**。
`scan` 和 `cross` 都只是形状筛，它们的命中不等于重复；`l1` 的 `DEFEQ` 是同文件内的硬
结论，跨文件只能给 `CROSS_*` 四档文本级证据——因为跨模块定义在 Agda 里不可能
definitionally equal（见 3.2）。且文本相同还不够：同名类型若在两文件里结构不同
（`CROSS_SHAPE`），仍不是同一命题；类型文本相同但符号来源不同（`CROSS_SCOPE`），量化域
不同、也不是同一命题；类型相同而证法不同（`CROSS_TYPE`）才是同一命题的两套证明，仍属
冗余。纯副本（`CROSS_COPY`）要求类型与定义体都逐字相同，本库当前 0 条。

---

## 2. 环境前提

```bash
agda  : PATH 上的 agda，否则回落 ~/.cabal/bin/agda   （本机 2.8.0）
stdlib: ~/.config/agda/agda-stdlib-<ver>/src        （由 --include 自动发现，不用手写）
categs: ~/.config/agda/agda-categories-<ver>/src    （同上）
仓库根: 当前目录 .                                  （先 cd 进仓库：agda 的 cwd 必须是仓库根，
                                                    才命中 _build/2.8.0/agda 接口缓存）
```

**下面所有命令都假设当前目录是仓库根**，所以 `--src ./src`、`--root .` 都相对它解析。
`--src ./src` 里 `--root` 是隐式推出来的（`dirname(src)`），显式写 `--root .` 更直观，
两者等价——实测输出一致（`files 244 decls 1991 prop-typed 1247 pairs 34 shape-groups 29`）。

**脚本放哪都行，`--root` 指的是仓库根。** 下面三件事最容易对不上：

| 现象 | 原因与改法 |
|---|---|
| `python3: can't open file '…/agda_dedup.py'` | 脚本不在当前目录。写成 `python3 src/agda_dedup.py …`（脚本在 `src/` 时）或绝对路径，其余参数不变 |
| `note: --root … 下没有 src/，已沿 .agda-lib 上溯到 …` | 正常提示，不是错误。在 `src/` 里写 `--root .` 时默认源目录会被拼成 `src/src`，工具沿 `.agda-lib` 自动找到真正的仓库根，结果照跑 |
| `✗ 源目录不存在：…`，rc=2 | 上溯也找不到带 `.agda-lib` 的祖先（或显式给了 `--src` 而目录写错）。显式 `--src` 时不自动修正——尊重你给的路径 |
| `l2` 报 `用例文件不存在` | `--cases` 要指真实文件（工具随附的样例是 `l2_cases_example.json`） |
| `note: 正在运行的是源目录内的副本 …` | 你把工具复制进了 `src/` 并从那运行。之前踩过：改完主副本忘了同步，跑的还是旧版，同一现象复现两次 |

早先这一层不校验时，`--root` 指错的默认行为是 `files 0 … 耗时 0.00 s` 且 rc=0——"跑通了"
和"扫了个空目录"看起来一样。现在要么自动修正并打 `note:`，要么硬报错退出 2。

实跑对照（同一份代码，三种 cwd）：

```
cd <repo>      && python3 src/agda_dedup.py scan --root .  --filter /Real  files 59  decls 816  pairs 9
cd <repo>/src  && python3 agda_dedup.py     scan --root .  --filter /Real
     note: 已沿 .agda-lib 上溯到 <repo>                                 →  files 59  decls 816  pairs 9
cd <repo>/src  && python3 agda_dedup.py     scan --root .. --filter /Real  files 59  decls 816  pairs 9
```

**工具放仓库内的 `tools/agda-dedup/`**——这样它跟被测仓库同一次 clone、同一次 push，
不用在两处之间同步。`tools/` 不在 `src/` 下，扫描只走 `src/`，不会被当成 Agda 源码扫。
装上启动器之后，在仓库根直接敲 `agda-dedup`：

```bash
mkdir -p ~/bin
printf '#!/usr/bin/env bash\nexec python3 "$HOME/<repo>/tools/agda-dedup/agda_dedup.py" "$@"\n' > ~/bin/agda-dedup
chmod +x ~/bin/agda-dedup
```

`~/.profile` 里已有 `$HOME/bin` 的 PATH 分支，新开终端即在 PATH 上（老终端 `source ~/.profile`）。
三种等价调法：

```
cd <repo> && agda-dedup scan --root .                        ← 装好启动器后，本文档所有示例都是这一种
cd <repo> && python3 tools/agda-dedup/agda_dedup.py scan --root .
cd <repo>/tools/agda-dedup && python3 agda_dedup.py scan --root ../..
```

克隆下来就能用：`git clone <repo> && cd <repo>`，然后上面第二行。工具目录里是三样文件：
`agda_dedup.py`、`使用说明.md`、`l2_cases_example.json`（L2 样例用例）。
探针落在 `<root>/_probe`，仓库根 `.gitignore` 里已有一行 `_probe/`。

`-i` 目录不用手写：脚本先读仓库根 `.agda-lib` 的 `include:`，再按
`AGDA_DIR` → `XDG_CONFIG_HOME/agda` → `~/.config/agda` 的顺序扫所有配置目录下的
`*/src`，名字匹配 `(agda-stdlib|agda-categories)` 或出现在 `depend:` 里的自动加进 `-i`。
`--include` 只在需要额外源目录时才用。
（Agda 2.8 仍认 `AGDA_DIR`：实测 `AGDA_DIR=/tmp/agdir2 agda -l std2` 能找到该目录
`libraries` 里登记的库，不设就报 `Library 'std2' not found`；写死 `~/.config/agda`
会在自定义环境里静默漏依赖，表现是探针 `NotInScope`。）

---

## 3. 四条命令，附实测输出

以下全部在 ALMA 工作副本上实跑过（2026-11-10，含 `d72d569` 之后的现状）。

### 3.1 `scan`：全仓候选

```bash
agda-dedup scan --root . --show 4
```

```
files 244  decls 1991  prop-typed 1247  pairs 34  shape-groups 29
  [1] +interchange @ Base/RationalRing.agda:49  <->  +-four-rearrange @ Wellspring/Prelude.agda:269
  [2] bracket-self @ Physics/Newton/Poisson.agda:102  <->  bracket-self @ Physics/Newton/QuadraticJacobi.agda:75
```

`d72d569` 删掉 4 条声明后，`decls` 从 1995 降到 1991、`pairs` 从 36 降到 34；
前两名也因此让位（`toℕ-natToFin` 与 `swap-sends-*` 已合并）。

读法：`decls` 是顶格声明总数，`prop-typed` 是类型里出现 `≡ ≤ < ≈ #` 且长度 > 6 的，
`pairs` 是形状分组内两两配对 + 同名跨文件补充去重后的总数，`shape-groups` 是形状种类数。

**`--all-types`：补 `--prop` 覆盖不到的整类。** 数据/函数定义（`n-at : ℕ → ℕ`、
`natToFin : (v : ℕ) → Fin (n-at v)`）过不了 `prop` 判据，探针也判不了（两个函数类型本来就
不 defeq），所以 `d72d569` 删掉的那批（`n-at`/`natToFin`/`toℕ-natToFin`）在这套候选池里
一条都看不见。补法是纯文本档：同名 → 跨文件 → 归一化定义体逐字相同。

```bash
agda-dedup scan --root . --all-types --show 12
```

```
all-types 非命题型 744 条，同名跨文件组 36，定义体逐字相同 9
  [copy] C₀ @ Cosmos/M/ListCosmos.agda:56  <->  Cosmos/M/ListSwap.agda:72
  [copy] ShapeOf @ Cosmos/ContCategoryLemmas.agda:111  <->  SketchPass/ContCategoryLemmas.agda:70
  [copy] shift @ Cosmos/Carried/SeqColimit.agda:49  <->  Cosmos/Carried/SeqColimitS.agda:46
```

这一档只说明"定义体逐字相同（纯副本）"，同一函数的不同写法看不出；删之前先看调用点。

**只扫 Real 层**（历史报告的同口径）：

```bash
agda-dedup scan --root . --filter /Real --show 4
```

```
files 59  decls 816  prop-typed 656  pairs 9  shape-groups 4
```

`--filter` 是**对绝对路径**做 `re.search`（`--src` 会被 `abspath` 展开，写成 `./src` 也一样），
所以要写 `/Real` 而不是 `^Real`——后者匹配不到，因为绝对路径以 `/…/<repo>/src/` 开头，
实测返回 0 文件。`/Real` 同时命中
`src/Real.agda`（顶层模块）和 `src/Real/` 整棵子树，共 59 个文件。

### 3.2 `l1`：判定义相等

```bash
agda-dedup l1 --root . --filter /Real --jobs 3 --out ./dedup_l1.json
```

实测（Real 层 9 对，`d72d569` 之后）：

```
files 59  props 656  pairs 9  ->  {'NEQ': 8, 'CROSS_NAME': 1}
```

全仓 34 对：

```
files 244  props 1247  pairs 34  ->  {'CROSS_SCOPE': 1, 'CROSS_SHAPE': 8, 'NEQ': 9, 'CROSS_NAME': 16}
```

`0 条 DEFEQ` 是**正确结果，不是失败**：`6c0d44c` 已把 6 组定义相等合并掉、别名删净。

全仓加 `--cross-file try`（34 对全编译，4 路 89 s）：

```
files 244  props 1247  pairs 34  ->  {'CLASH': 23, 'NEQ': 10, 'SCOPE_ERROR': 1}
```

这不是变差，而是 `try` 的**固有限制**：23 条 `CLASH` 全是 A、B 两文件本来就有同名声明
（`CROSS_SHAPE` 那 8 条 `bracket-*`、`jacobi` 之类），把 B `open import` 进 A 的副本后
必然 `Multiple definitions`；1 条 `SCOPE_ERROR` 是两边都 `open` 了同名算子
（`_<_` 报 `AmbiguousName`）。这一类候选**编译探针判不了**，只能靠 `skip` 模式的
`CROSS_*` 档给结构结论——所以默认就是 `skip`。

`CROSS_COPY` 现在是 **0 条**，这不是"库里没有重复"，是两层判据修好之后的真实结论：
ALMA 里没有任何两条跨文件声明是"类型 + 证明体都逐字相同"的纯副本。原先的 3 条里，
`d72d569` 合并掉的 `toℕ-natToFin`、`swap-sends-*` 确实是同题同证（两边都 `= refl`，
已用旧文件复验 `body same=True`），但 `+interchange` 连"同一命题"都不成立（见 3.2）。

#### 关键前提：跨模块定义永远不"相等"

Agda 的 definitional equality 只在同一模块命名空间内有意义。`A.foo` 与 `B.foo`
即使源码逐字相同，也是两个独立常量，`A0.foo != foo` 恒成立（实测三条：`A0.natToFin v
!= natToFin v`、`Obs !=< A0.Obs`、`A0.≈M t != f ≈M f`）。所以：

- **同文件候选**：`l1` 走探针有效，能判 `DEFEQ` / `NEQ`。
- **跨文件候选**：`l1` 原理上给不出"相等"，只会给撞名或恒假的不等。

因此 `l1` 现在对跨文件候选**不编译**，改成比对类型文本（去注释压空白）与整段定义体
（声明行到下一个**新声明行**，声明名归一化），再按证据强度分成五档：

| 类别 | 判据 | 含义 |
|---|---|---|
| `CROSS_NAME` | 类型文本不同 | **语义未判定**：文本不等不等于命题不等（显式/隐式写法、α 改名、中缀 vs 前缀都会让文本变而命题同一）。待定档，需探针或人工复核 |
| `CROSS_SHAPE` | 类型相同，但同名 record/data 的字段列表不同（且该 record 与被比类型确有牵连） | **同形不同义**：搭在不同数据类型上，是平行实现，不可合并 |
| `CROSS_SCOPE` | 类型文本相同，但同一个符号来自不同模块 | **字面相同、量化域不同**（一侧 `+` 是 ℚ 加法、另一侧是 ℕ 加法），不可合并 |
| `CROSS_TYPE` | 类型相同、定义体不同 | 同一命题的两套证明，**仍是冗余**（本库当前 0 条） |
| `CROSS_COPY` | 类型与定义体都逐字相同 | 纯复制品，可合并或改 re-export（本库当前 0 条） |

判据顺序按"证据有多硬"排：字段表（`SHAPE`）与符号来源（`SCOPE`）都是可从源码直接
读出的确定事实，排在前；"证法是否相同"（`TYPE`）与"字是否一样"（`COPY`）是文本推断，
排在后。`NAME` 不在"证据"序列里——它是**没判**，不是判成"不重复"。

`CROSS_SHAPE` 挡的是"类型文本里被隐式推断掉的数据类型"：`Poisson` 与 `Quadratic*`
各有一个 `Obs`（3 字段 vs 6 字段），而类型都写着 `∀ f → bracket f f ≡ zero`。
`CROSS_SCOPE` 挡的是更深一层——**类型里连类型标注都没有**：

```
+interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
```

`a b c d` 全无标注，量化域由 `_+_` 隐式决定。`Base/RationalRing` 的 `_+_` 来自
`Data.Rational`（ℚ），`Wellspring/Prelude` 的 `_+_` 来自 `Data.Nat.Base`（ℕ）。
**两串字一模一样，命题却完全不同。**

`--cross-file try` 仍可强制搭探针跑跨文件候选，但它在跨文件上基本**测不出东西**：探针
把 A 的模块体整段复制后再 `open import B`，两套 import 落进同一作用域——`using` 叠加
即 `Ambiguous`（实测 `_<_` 二义 → `SCOPE_ERROR`），B 与 A 有同名声明则直接
`ClashingDefinition`（`CLASH`）。这两个档都表示"这对没测到"，不是判据。所以跨文件
不要靠 `try` 补结论；真要跨文件判等价，得换成"两侧限定名"的新探针（`open import A as
α` / `open import B as β`，类型两侧都写限定形式），现在没做。

#### 跨文件三对的历史记录（`CROSS_COPY` 现为 0 条）

| 命题 | 位置 A | 位置 B | 判定 |
|---|---|---|---|
| `+interchange` | `Base/RationalRing.agda:49` | `Wellspring/Prelude.agda:269`（名字叫 `+-four-rearrange`） | **`CROSS_SCOPE`**：ℚ 的四项重排 vs ℕ 的四项重排，**不是同一命题，不该合并** |
| `toℕ-natToFin` | `Cosmos/Carried/LimitSystem.agda:82` | `Cosmos/Carried/LimitSystemS.agda:63` | `CROSS_COPY`（体逐字相同），已合并（`d72d569`） |
| `swap-sends-0→1` | `Cosmos/M/ListSwap.agda:331` | `Cosmos/M/ListSwapDef.agda:239`（名字叫 `flip-sends-0→1`） | `CROSS_COPY`（体逐字相同），已合并（`d72d569`） |

**这里连续改判了两次，最后一条是这轮才查清的。** 过程值得留着：

第一次（旧 `decl_body`）说三条都是 `CROSS_COPY`——错的，边界 bug 让每条只取到类型行。
第二次（修边界后）说 `+interchange` 是 `CROSS_TYPE`（同题异证）——**仍然错的**，两者
只是类型文本相同，命题不同。第三次（加 `CROSS_SCOPE`）才落到真相：

```
Base/RationalRing.agda:14   open import Data.Rational      using (… _+_ …)   ← ℚ
Wellspring/Prelude.agda:38  open import Data.Nat.Base      using (… _+_ …)   ← ℕ
```

两条的类型文本 `∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)` **逐字相同**，因为
`a b c d` 没有任何类型标注，量化域完全靠 `_+_` 隐式决定。**一个是 ℚ 上的定理，一个是 ℕ
上的定理，名字不同、证法不同、对象也不同。**

所以**合并 `+interchange` 是错的**：`Wellspring/Beings.agda:803` 用的是 ℕ 上下文，
换到 `Base.RationalRing` 的 ℚ 版本会直接改语义。此前"合并它仍然正确"的说法作废。

已合并的两条经 `git show d72d569^` 取出旧文件复验，确实是纯副本：

```
toℕ-natToFin (LSS 旧) : typ same=True  body same=True  scope=[]
swap-sends-0→1(旧)    : typ same=True  body same=True  scope=[]   ← 与 flip- 异名同证
```

所以 `d72d569` 那两条的处置是对的，只是 `+interchange` 这条不能跟着一起合。

`d72d569` 实际做法（2026-11-10）：

- `LimitSystemS.agda` 删掉自带的 `natToFin` + `toℕ-natToFin` 两份，改成
  `open import Cosmos.Carried.LimitSystem using (n-at; natToFin; toℕ-natToFin)`
  —— 即**保留旧内核 `LimitSystem` 为规范版**，新内核 `LimitSystemS` 取用。
- `ListSwap.agda` 删掉 `swap-sends-0→1 : fwd e0 ≡ e1` / `= refl`，保留
  `ListSwapDef.agda` 的 `flip-sends-0→1`。
- 三个文件（`LimitSystemS` / `ListSwap` / `Real/Convergence`）逐个 `agda -i src
  --double-check` 实测 `rc=0`、0 error。

剩下 `+interchange` 的合并成本（已勘察，不轻）：

| 条目 | 引用现状 | 卡点 |
|---|---|---|
| `+interchange` | `Base/RationalRing` 内部 3 处 + `Physics/Quantum/Rotation` 4 处 + `AmplitudeComp` 2 处；`+-four-rearrange` 只被 `Wellspring/Beings.agda:803` 用 1 次 | `Wellspring/Prelude.agda` **不 import** `Base.RationalRing`，改别名会新引入一条依赖；要删就得把 `Beings` 的引用改向 `Base.RationalRing` |

另有一条**同名第三份**不在上表：`Cosmos/M/ListCosmos.agda:204` 也叫 `swap-sends-0→1`，
但类型是 `FiberAdjˢ.to (FMapˢ.adjFˢ (FMˢ.mor swapFMˢ) i0 d0 i0) e0 ≡ e1`，与 `fwd e0 ≡ e1`
不同——不是副本。它因为写成冒号后换行（`swap-sends-0→1 :`），`DECL` 收不到，所以没进
候选（坑 15 的直接实例：漏收不只会少统计，还会让同名不同义的声明逃过配对）。

#### 8 条 `CROSS_SHAPE`：块同字，但类型不是同一个

`Physics/Newton/Poisson.agda` 的 8 条与 `Quadratic{S,Skew,Jacobi,Bilinear}.agda` 中的同名
声明，声明块逐字相同，但两边用的是**不同的 `Obs`**：

```
Physics/Newton/Poisson.agda    record Obs { c a b }         -- 3 字段，仿射观测量
Physics/Newton/Quadratic.agda  record Obs { c a b d e f }   -- 6 字段，二次观测量
```

`Quadratic*` 系列 import `Quadratic` 取 `Obs`/`bracket`，`Poisson.agda` 则**不 import**
任何 `Quadratic*`（全仓只有 `Everything.agda` import `Poisson`），两边各自定义
`bracket`/`zero`/`add`/`scale`/`neg`/`pO`/`qO`。类型文本 `∀ f → bracket f f ≡ zero` 里
连 `Obs` 都没有——它是 Agda 从 `bracket : Obs → Obs → Obs` 隐式推出来的，只比字面
必然误判。这 8 条涉及 `bracket-self/skew/qp/addˡ/addʳ/scaleˡ/scaleʳ` 与 `jacobi`，
**不能合并**：它们是同一套证明模板在两种观测量代数上各写一遍。

#### 16 条 `CROSS_NAME`：文本不同，逐条复核后确为不同命题

（工具这一档只给"文本不同"，不下语义结论。下面这些判断是**人工读源码得到的**，
不是工具的输出。）

- `≈M-refl/sym/trans`（`Base/MCorr.agda` 的 `{I : Set i}{A : I → Set a}` 泛型版 vs
  `SketchPass/ContCategory.agda` 的 `Container` 版）、`∘M-assoc`（`_≈sr_` vs `≈M`）、
  `shape-eq-*` 5 条（内部全用 `≈sr` vs `≈M`）——两套等价体系，`SketchPass` 是早期草案，
  不是同一命题。
- `double-half`（`twoℚ * halfℚ ≡ 1ℚ` 常值 vs `(x : ℚ) → (x + x) ÷ embed 2 ≡ x` 函数型）、
  `pythagoras-345`（`u₃₄₅/v₃₄₅` 的 `norm²` vs `c₃₄₅*s₃₄₅`）、`≈-refl/sym/trans`
  （`Real` 的 `x ≈ x` vs `Wellspring` 的 Stream 版）——同名不同命题。
- `≈-<-respʳ`（`y ≈ℝ z → x <ℝ y → x <ℝ z`）vs `≈-<-resp`（`x ≈ℝ y → x <ℝ z → y <ℝ z`）
  ——左右侧不同，两条互补引理。
- `toℕ-inject₁^d`（`inject₁^d d {m} x` vs `inject₁^d d x`）——隐式参数显隐不同。

#### 9 条 `NEQ`（同文件，探针有效，确实不等）

`le-addˡ/ʳ`（`Real/Interval/Mul.agda`）、`distribˡ/ʳ-rec2/rec3` 六对
（`Real/Interval/Mul/Laws.agda`）、`mkCoherenceProof/mkDissipationProof`
（`Wellspring/StandardModel.agda`）。这些不是别名，不能合并。

Real 层那 1 条 `CROSS_NAME` 是 `≈-<-respʳ/resp`，属上表最后一类。

### 3.3 `l2`：替换实验

先写用例 JSON（格式见第 5 节），再跑：

```bash
agda-dedup l2 --root . \
  --cases tools/agda-dedup/l2_cases_example.json --probe ./.probe_l2 --jobs 2
```

实测（`l2_cases_example.json` 的 4 条）：

```
cases 4  ->  {'REPLACED': 4}
### cancelr  [REPLACED]  Real/Interval/Mul.agda:cancelʳ
### double   [REPLACED]  Real/Interval/Abs.agda:double-≤
### reassoc  [REPLACED]  Real/Interval/OrderLe.agda:reassoc
### plus1    [REPLACED]  Real/ConvergenceLaws.agda:plus1
```

`REPLACED` 只说明「这条命题能由目标库那几个定理直接给出」，**不说明原库抄了目标库**。

探针的作用域：case 里写了 `imports` 就用它；不写就先用内置的 ℚ 模板。模板跑不通
（`NotInScope` / `Ambiguous` / `ParseError`——都不是「证不出来」，是「名字没进视野」）
时，自动换成**被测文件自己的顶层 import 块**再编一次，用例里会留
`"probe_variant": "file-imports"`。两套 import **不能合并**：合起来会把
`Data.Nat._+_` 和 `Data.Rational._+_` 同时打开，直接 `Ambiguous`。
`rhs` 写成完全限定名（`Data.Nat.Properties.+-comm`）时，它的模块会被自动
`open import` 进来。
判读口径（和 `语义等价审计报告.md` 第八节一致）：

- 替换体**比原证明短得多、且用的是别的定理** → 真重复，值得删；
- 替换体只是把原证明里本来就用的那几个引理（`+-assoc`/`+-inverseˡ`/`+-mono-≤`）
  串成一行 → **排版重复**，删掉不减少定理量。

上面 4 条全是排版重复。曾经的唯一真重复 `≤∧<⇒⊥`（`Real/Convergence.agda:89`）
已在 `6c0d44c` 里直接改用 stdlib 的 `≤⇒≯` 并删掉定义，现在该声明不存在，
旧用例里的 `lelt` 已从示例 JSON 移除（原位置 `:89` 现在是 `nonneg-no-pos`，
`:91` 就是 `⊥-elim (≤⇒≯ 0≤x x<0)`）。

### 3.4 `cross`：与 stdlib 比形状

```bash
agda-dedup cross --root . --filter /Real --drop-qualified
```

实测：

```
Real 层:  mine prop-typed 656   pure-shared-vocab 304  target prop-typed 3613  shape hits 1
全仓:     mine prop-typed 1247  pure-shared-vocab 336  target prop-typed 3613  shape hits 1
```

唯一命中是 `≈-trans @ Real.agda:349 ↔ _⊙_ @ Tactic/RingSolver/.../Reasoning.agda`——
形状碰巧相同，语义无关，教科书级假阳性（`≈-trans` 是关系传递性，`_⊙_` 是多项式乘法）。
加上 `--body` 之后连这 1 条也没了（见下），**与 stdlib 的真重复是 0 条**。

`--body` 是放宽 `--prop` 之后唯一还有意义的口径。分三层看：

| 口径 | mine | shared | target | hits |
|---|---|---|---|---|
| 默认命题型 | 1247 | 336 | 3613 | 1 |
| `--prop='.*'`（全量签名） | 1896 | 495 | 9545 | **185** |
| `--prop='.*' --body`（签名 + 定义体） | 1896 | 495 | 9545 | **0** |

`--prop='.*'` 的 185 条全是垃圾：`shift : ℕ → ℕ → ℕ` 一个就对上 `_⊔_`/`_⊓_`/`_^_`/
`∣_-_∣`/`_P_`/`_C_` 十几个 stdlib 函数，`up ↔ fsuc` 同理。**同签名不等于同东西**——
`ℕ → ℕ → ℕ` 这种骨架在 stdlib 里有几百个，形状匹配在这个粒度上没有任何区分力。
加上定义体逐字比对（`--body`，实测 1.5 s，`read_src` 有缓存）后归 0。

所以"查全量代码与 stdlib 的重复"这件事，工具能做，答案是 **0 条**：ALMA 全仓 1991 条
声明对 stdlib 9647 条，类型形状相同 478 对，其中类型与定义体都逐字相同的 **0 对**。
（`decls` 仍是 1991：`--prop` 只筛"命题型"，`record`/`data` 本来就不进 `DECL` 集合，
放宽它也收不进来——这是 `DECL` 的形态限制，不是冒号。）

`--drop-qualified` 剔掉类型里出现 `X.y` 限定访问的条目（`RealI.l` 这类字段泄漏会
把库内特有结构伪装成外来词汇）；不加它时 Real 层 656 条里 313 条算"纯共享词汇"，
加了只剩 304——只砍掉 9 条，说明字段泄漏在这一层并不严重。

口径提醒：这里的 `pure-shared-vocab` 判据是「类型里不含任何本库定义的**顶格**名」。
record 字段名、`field` 块里的名字不在这张表里，所以 304 比历史手工口径的 172 宽；
`target prop-typed 3613` 也比历史 3979 少（历史把 stdlib 的 `where` 内定义也算进去了）。
**能比的只有结论（0 真重复），不能逐个比数字。**

两条防线别混：`pure-shared-vocab`（上面这条）挡的是**本库特有对象**混进跨库比对，
历史那次 `_≈ℝ_` vs `_*ℝ_` 的假候选就是它挡掉的；`--drop-qualified` 挡的是另一件事
——record 字段/限定访问泄漏（`RealI.l` 之类）。两者独立，关掉任一条都不会让另一条失效。

---

## 4. 公共参数

| 参数 | 默认 | 说明 |
|---|---|---|
| `--src` | `<root>/src` | 源目录，可重复给多个 |
| `--root` | `--src` 的父目录（不给 `--src` 时就是 `.`） | agda 的 cwd；必须是仓库根，否则丢接口缓存、全链重编译 |
| `--include` | 自动发现 | 额外 `-i`；默认先读仓库根 `.agda-lib` 的 `include:`（相对根的源目录，ALMA 是 `include: src`），再扫配置目录 `AGDA_DIR` → `XDG_CONFIG_HOME/agda` → `~/.config/agda` 下的 `*/src`，按 `(agda-stdlib\|agda-categories)` 与 `depend:` 匹配（路径仍按传统布局解析，vendored / nix 依赖要给 `--include`） |
| `--safe` | 关 | 编译探针时加 `--safe`（禁 `postulate` / `NON_TERMINATING` 这类信任后门）。**ALMA 的模块头本身已有 `{-# OPTIONS --safe ... #-}`，探针原样复制模块头，所以本库无需开这个开关**（实测 9/9 探针都带 `--safe`）。被测库若不 safe，开了会立刻整链失败——实测含 `postulate ax : Set` 的样本加 `--safe` 报 `[SafeFlagPostulate] Cannot postulate ax with safe flag`，不加则 `rc=0` |
| `--probe` | `<root>/_probe` | 探针目录；每个用例一个 `Q_<tag>.agda`，同名覆盖。**默认在仓库内**（一轮 l1 落几十个文件，记得加进 `.gitignore`）；早期默认是 `<root>/../audit/probe_dedup`，会写到 clone 外面、多仓库共用还会互相覆盖 |
| `--agda` | PATH 上 `agda`，否则 `~/.cabal/bin/agda` | 可执行路径 |
| `--jobs` | `4` | 并行编译数。**不要调到 8**：冷缓存 8 路会把机器压到 `ls` 都排不上（已两次中止） |
| `--filter` | 空 | 只处理绝对路径 `re.search` 命中的文件，可重复 |
| `--prop` | `(≡\|≤\|<\|≈\|#)` | 命题型判据；扫别的层（如 Setoid 用 `≈`）可改 |
| `--show` | `20` | 人读输出最多列几条 |
| `--max-cases` | 空 | 只跑前 N 个候选，用来快速验通路 |
| `--cross-file` | `skip` | 仅 `l1`：`skip` 时跨文件候选不编译，走 `CROSS_NAME / SHAPE / SCOPE / TYPE / COPY` 文本比对；`try` 强制搭探针（结果不可信） |
| `--all-types` | 关 | 仅 `scan`：补一档非命题型的文本比对（"同名跨文件 + 定义体逐字相同"，见 3.1 末尾）。不进编译，0.5 s |
| `--out` | 空 | 落 `{"report": {...}, "cases": [...]}` 结构 JSON；`report.elapsed` 是本次耗时（秒，一位小数），终端也会打一行 `耗时 X.XX s` |

计时落在 `report.elapsed` 而不是只打印：CI 里日志会被截断、混排，"这次比上次慢多少"
只有 JSON 里的数字稳定可读。实测口径（v13.3，`--jobs 4`）：`scan` 0.58 s、
`l1 --cross-file skip` 全仓 32.4 s、`l2` 四例 17.0 s、`cross --body` 1.6 s。

`l2` 独有：`--cases`（必填）、`--imports`（覆盖默认 import 块，`\n` 分行）。
`cross` 独有：`--other`（目标库 src，默认自动找 stdlib）、`--drop-qualified`、
`--body`（形状对上后再比整段定义体；跨库真副本只在这个口径下成立，见 3.4）。

---

## 5. L2 用例 JSON 格式

下面用 `//` 标出字段含义，**那只是本说明的标注，JSON 不支持注释**；实际文件请照
`work/l2_cases_example.json` 的写法（纯 JSON，已验证可被 `json.load` 读取）：

```json
[
 {
  "tag":  "cancelr",                          // 必需，探针文件名 Q_<tag>.agda
  "file": "Real/Interval/Mul.agda",           // 必需，相对 --src
  "name": "cancelʳ",                          // 必需，源文件里的顶格声明名
  "clause": "x y",                            // 可选，具名子句（首参隐式时写 {x} 0≤x）
  "rhs":  "trans (+-assoc x (- y) y) ...",    // 必需，等号右边的证明体
  "imports": "open import ..."                // 可选，整块覆盖默认 stdlib import
 }
]
```

生成出的探针长这样（`{-# OPTIONS #-}` 从源文件原样复制）：

```agda
{-# OPTIONS --safe --cubical-compatible --guardedness #-}

module Q_cancelr where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _≤_; _<_; ∣_∣)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; ≤⇒≯
  ; +-assoc; +-identityʳ; +-identityˡ; +-inverseˡ; +-mono-≤; nonNegative⁻¹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥)

-- 原定义：Real/Interval/Mul.agda:60
audit : ∀ x y → (x - y) + y ≡ x
audit = λ x y → trans (+-assoc x (- y) y) (trans (cong (x +_) (+-inverseˡ y)) (+-identityʳ x))
```

默认 import 块是 ℚ 专用。测其它层（ℕ / ℤ / RealI / Setoid）时逐 case 写 `imports` 覆盖。

三个写法要点（都是踩出来的）：

1. **首参隐式别用 `λ {x} 0≤x → ...`**，要用具名子句 `"clause": "{x} 0≤x"`。
2. **具名隐参的名字要查真名**：`+-mono-≤` 是 `{x}{y}{u}{v}`，`≤-trans` 是 `{i}{j}{k}`
   （不是 `{p}{q}{r}`）。写错报 `WrongNamedArgument`。
3. **别用 `_` 占位**，会 `UnsolvedMetaVariables`；隐式能推就省、不能推就给真名。

---

## 6. 判定语义

### L1（`DEFEQ` / `NEQ` / `CLASH` / `SCOPE_ERROR` / `OTHER` / `CROSS_*`）

探针只在**同文件**候选上用：在被测模块副本尾部追加

```agda
-- === AUDIT <tag> ===
chkT′ : (A) → (B)
chkT′ z = z
```

`z` 的静态类型是 A，却要对上 B；只有 A 与 B **定义相等**才通过。α 重命名、隐式/显式 Π
差异由 Agda 自己吸收。判的是类型相等，不是证明体相似。跨文件候选不进探针，改走
`CROSS_*` 文本比对（理由见 3.2）。

探针名**不能叫 `chkT`**：被测模块自己定义了 `chkT` 时，追加进去会报
`[ClashingDefinition] Multiple definitions of chkT`（实测 rc=42），而这一档会被归成
`CLASH`——本可判 `DEFEQ` 的一对会被贴成“跨文件撞名”。`′` 结尾是普通标识符（不是
`_` 开头的运算符），实测 `chkT′` 在同样场景下 `rc=0`、`DEFEQ`。

探针名的避让范围必须覆盖**被测文件 import 链上的名字**，不能只看文件文本。反例：
`audit/coll4/A4.agda` 自己不写 `chkT′`，但 `open import CH` 把 `CH.chkT′` 转了出来，
探针仍叫 `chkT′` 就报 `Multiple definitions of chkT′` → `CLASH`。包模块也绕不过去：
`module _ where` 与 `module AuditProbe_<tag> where` 里的同名声明一样报 `Multiple definitions`
（Agda 不允许在内层作用域重定义已 `open import` 的名字，两种都实测过）。
现在的做法是 `visible_names`：把「被测文件自己的声明 ∪ 它 import 链上 depth 2 的模块声明」
并成占用集，从 `chkT′` 起取第一个不在集合里、也不在文件文本里的名字。`coll4` 实测取到
`chkT′1` → `DEFEQ`；`coll3`（两边自带 `chkT′`）同样 `DEFEQ`。用到的名字记在
`cases[].probe_name`。depth 2 之外的 `public` 链极罕见，真撞了会显式报 `CLASH`，不静默。
上例只是最常见的形态。

| 分类 | 判据 | 含义 |
|---|---|---|
| `DEFEQ` | `agda` exit 0 | 两命题定义相等 → 真重复，可合并 |
| `NEQ` | 报错行号 ≤ `marker + 2` **且**输出含 `!=` / `does not reduce to` | 探针自身不过 → 命题不等 |
| `CLASH` | 输出含 `ClashingDefinition`（只在 `--cross-file try` 下出现） | 探针里 A、B 撞名，**这对没被测到**，结论无效；若撞的是探针名会自动换名重试（≤3 次），三次仍撞才落这一档 |
| `SCOPE_ERROR` | 输出含 `NotInScope` / `Ambiguous`（只在 `--cross-file try` 下） | 探针环境没搭好，结论无效，要查 |
| `OTHER` | 其余 | 报警在模块体里（源文件自己就编不过），或 `UnequalSorts` 之类；首条错误的 `[标签]` 进 `other_tag` |
| `CROSS_COPY` | 跨文件，类型与定义体都逐字相同 | 纯复制品，可合并（本库 0 条） |
| `CROSS_SHAPE` | 跨文件，类型相同但同名 record/data 字段不同 | 同形不同义，平行实现，不可合并（本库 8 条） |
| `CROSS_SCOPE` | 跨文件，类型文本相同但符号来自不同模块 | 量化域不同（ℚ vs ℕ），不是同一命题（本库 1 条） |
| `CROSS_TYPE` | 跨文件，类型文本相同、定义体不同 | 同一命题两套证法，冗余（本库 0 条）；`err` 带双方体前 60 字符 + 首个差异位置与附近切片 |
| `CROSS_NAME` | 跨文件，类型文本不同 | 语义未判定（文本不等 ≠ 命题不等）；待定档，`err` 写的是"需探针或人工复核" |

`CROSS_TYPE` 的 `err` 现在给出两段证明的开头（`A: … | B: …`，名字已归一为占位符），
再跟一个是**首个差异位置 + 附近切片**——长证明前 60 字符往往一模一样，真正分叉在
200 字符开外，只看开头等于让人自己翻文件。实现是 `body_diff()`（`difflib.SequenceMatcher`
取首个非 equal 块，往前 8 / 往后 40 字符）。样例实测：
`类型相同但定义体不同：同一命题的两套证明  A: NAME:true≡trueNAME=refl | B: …symrefl
  首差 A@21「ueNAME=refl」 | B@21「ueNAME=symrefl」`。

跨文件那五档的判据顺序是 `CROSS_NAME → CROSS_SHAPE → CROSS_SCOPE → CROSS_TYPE → CROSS_COPY`：
前两档（字段表、符号来源）是能从源码直接读出的确定事实，排在"证法是否相同"之前。

判据顺序固定：`rc == 0` → `DEFEQ`；`ClashingDefinition` → `CLASH`；`NotInScope`/
`Ambiguous` → `SCOPE_ERROR`；行号 + `!=` 双条件 → `NEQ`；余下 `OTHER`。跨文件候选在
编译前就被分流到 `CROSS_*`，不进这套判据。

`NEQ` 的双条件是必需的：`CLASH` 报错行号落在模块体内部，而模块体在 marker 之前，
行号必然 ≤ `marker + 2`——只看行号会把所有撞名的对判成"不等"（历史实测 25/36 中招）。
`CLASH` 必须单列，因为它的成因是探针构造（复制模块体 + `open import B`）而非命题本身。

`CROSS_*` 四档的存在理由见 3.2：跨模块定义不可能 definitionally equal，探针在这个
场景下**结构性地**失效，只能退到文本层面回答"是不是同一句话抄了两遍"。而"同一句话"
本身也有陷阱：类型文本会漏掉被隐式推断的类型，所以还要比同名 record 的字段结构
（`CROSS_SHAPE`）。

`SCOPE_ERROR` 历史实测一条：`+interchange @ Base/RationalRing.agda:49` 与
`Wellspring/Prelude.agda:269` 的 `+-four-rearrange`。原因是两个模块各自 `open import`
了不同的 `Data.Rational.Base`，合并进一个探针后 `0ℚ`、`_<_` 出现 `Ambiguous`：

```
Ambiguous ... a data type Data.Rational.Base._<_ brought into scope by
  - the opening of Data.Rational at Q_uinterchange....agda:15.13-26
  - the opening of Data.Rational.Base at ...
when scope checking 0ℚ < 1ℚ
```

改用文本比对后发现这对**类型文本逐字相同**，但两侧的 `_+_` 分别来自
`Data.Rational`（ℚ）与 `Data.Nat.Base`（ℕ），属 `CROSS_SCOPE`——探针环境不兼容把它
完全掩盖了。这也是为什么跨文件不能只靠编译结论。

### L2（`REPLACED` + 8 种失败码）

按输出里第一个出现的错误关键字分类，命中顺序固定：

| 码 | 常见成因 |
|---|---|
| `REPLACED` | exit 0 |
| `ParseError` | 括号少一个、token 缺失。**本次实测就踩了一次**：`plus1` 的 rhs 少一个 `)` |
| `NotInScope` | 目标库没有这个名字，或 `open import` 没 re-export（ALMA 模块默认不 re-export 导入名） |
| `InfectiveImport` | 探针没带源文件那套 `OPTIONS`，`--guardedness` 判定不一致 |
| `UnsolvedMetaVariables` | rhs 里用了 `_` 占位 |
| `NoParseForApplication` | 把带参定理当值直接赋给函数型 `audit`（如 `audit = ≤⇒≯`） |
| `WrongNamedArgument` | 具名隐参名写错（见第 5 节） |
| `TypeError` | 类型对不上，通常是目标定理的序关系方向或参数顺序不同 |
| `FAILED` | 其它 |
| `NOT_FOUND` | 用例里的声明在本库已不存在（被删/改名）。**不再整批退出**：坏用例记这一档，其余照跑（`d72d569` 删 `≤∧<⇒⊥` 后实测 `cases 5 -> {'NOT_FOUND': 1, 'REPLACED': 4}`） |

失败时脚本会打 `err:` 一行（截断 180 字符），完整 400 字符在 `--out` 的 JSON 里。

---

## 7. 已知边界与坑

按"会直接导致结论错误"排序：

1. **一个探针只测一对。** Agda 每份文件只报首个错误；早期把多对合并进同一探针，
   结果后面的全落 `OTHER`。所以 `l1` 是每对一份 `Q_<tag>.agda`。
2. **追加的 `chkT` 必须与模块体的块列对齐——不是"Agda 要求顶格"。**
   这一点容易被误读成语言约束，实际不是。`module X where` 的 layout 块列由**块内第一个
   token 决定**：模块体首行缩进 2 格，块列就是 3，后面所有声明都写在 3 上，**完全合法**。
   本工具把 `chkT` 追加在第 1 列，所以只支持顶格模块体；缩进体时 `chkT` 落在顶层模块
   之外，报的是 `DeclarationsAfterTopLevelModule`（不是 parse error，也不是 `NotInScope`）。
   实测（一个临时目录里三份手写文件，`Ind / Ind2 / Ind3`）：

   ```
   Ind   缩进模块体（无探针）                      -> rc=0
   Ind2  缩进模块体 + 与块列对齐的 chkT            -> rc=0     ← 缩进探针本身可行
   Ind3  缩进模块体 + 顶格 chkT                    -> rc=42
          error: [DeclarationsAfterTopLevelModule]
          No declarations allowed after top-level module.
   ```

   所以"必须顶格"是**本工具的实现选择**，不是 Agda 规则；技术上只要按块列缩进追加
   `chkT` 就能支持缩进体。真正的代价不在探针，而在**候选来源**：`parse_file` 只收顶格
   声明，缩进风格的库连候选都收不满。实测 `agda-categories-0.3.0`：
   **顶格 933 条 / `module _` 体内 560 条**，工具只看到 74%——这是静默低覆盖，比报错更
   危险。现在 `scan` / `l1` 在 `module _` 体内声明超过顶格 10% 时会打一行 `note:`，把这层
   暴露出来。（旧值是 1268 / 42%：把块头续行、`private` 里层、以及签名里带 `{X = CS}`
   这类记录赋值的行都算错了，见第 830 行一带的说明。）

   **不要为了"支持缩进声明"把源码拍平成顶格**（评审常见建议）：拍平等于把缩进体声明挪到
   第 1 列，正是上面 `Ind3` 的形态，`rc=42 DeclarationsAfterTopLevelModule`，整份探针直接
   非法；而且它同时毁掉 `record` / `where` / `let` 的嵌套结构。探针本来就是整段复制原文件，
   缩进声明**不需要**拍平也能被 Agda 编译——缺的只是解析器看不看得见它们。
   直接"把缩进行全收进候选"也不可行：ALMA `src` 实测缩进行 **6705** 条，其中 **1579 条
   （23.6%）** 是 Π 绑定、record 参数、`where` 子句、`...` 模式行，例如
   `{Idx : Set ℓᵢ} {Sh : Idx → Set ℓₐ}`，会被 `DECL` 当成名叫 `{Idx` 的声明；
   历史模拟把 6652 条全收进来时，候选 1247→3657，第一条候选是
   `(t @ Cosmos/Carried/DetColimit.agda:37`（绑定名被当声明名）。所以现在是**告警不收集**。

   早期 `layout_t/Q_ind2.agda` 的 ParseError 是另一回事：它在顶格 `open import` 之后又
   接了更深缩进的 `bar`，块列已被顶格行定成 1，`bar` 越界才报错——那是**块内缩进不一致**，
   不是"缩进探针不可行"。
3. **编译 cwd 必须是仓库根。** 在探针目录里编会全链重编译并报
   `Categories.Category.Core FileNotFound`。脚本固定 `cwd=ctx['root']`。
4. **并行 ≤ 4。** 冷缓存 8 路会 load 13，机器压满。另一点没有实测证据但值得防：Agda 写
   `.agdai` 不是原子的，多探针同时触发同一依赖重编译时有写坏的窗口。本机 `.agdai`
   全热，没遇到过；冷缓存上跑大批量时降到 2–3 路更稳。
5. **`l1` 用 `chkT : (A ≡ B)` 写法的替代方案不行。** 大类型经顶格中间定义会
   `UnequalSorts`（一次爆 20 条）。必须用现在这个 `(A) → (B)` + `z` 的形式。
6. **`--double-check` 要剥掉。** 源文件里的 `{-# OPTIONS --double-check #-}` 若带进探针，
   每条都要重检整棵依赖，慢到不可用；脚本已在复制时剥掉。
7. **`--filter` 是对绝对路径 `re.search`。** 写 `^Real` 拿不到东西（实测 0 文件），要写 `/Real`。
8. **`--drop-qualified` 的误伤。** 类型里出现 `X.y` 就整条丢；如果某个库的合法记号
   里带点（少见），会被错误剔除。
9. **`cross` 的 target 解析依赖同一套顶格规则。** 目标库若大量使用 `where`/`module _`
   内的定义，声明数会偏低（stdlib 实测 3613 对历史 3979），只影响绝对数字，不影响 0 命中的结论。
10. **`scan` 的 α 重命名只动 Π 绑定名。** 它**不抹**运算符和类型名——这是故意的：
    早期那版抹了，导致 `_≈ℝ_` 与 `_*ℝ_` 被当成同一形状，产生假候选。
    代价是：形状不同的同义命题（如 `a ≤ b → b < a → ⊥` 与 `_≯_` 写法）永远提不出来，
    只能靠 `l2` 抓。
11. **`l2` 的 `--imports` 默认只覆盖 ℚ。** 非 ℚ 的用例（`Nat` / `Stream` / 自建 prelude）
    要么逐 case 写 `imports`，要么靠自动回退：模板编不过（`NotInScope`/`Ambiguous`/
    `ParseError`）时改用被测文件自己的 import 块重编，用例记 `probe_variant: file-imports`。
    实测一条 `Nat` 的 `+-comm` 用例，不写 `imports` 也能 `REPLACED`。
12. **探针目录不会自动清。** 默认是仓库内的 `<root>/_probe`（记得 gitignore）；同名 tag
    覆盖写，改 tag 会留旧文件；想干净就 `rm -rf <probe>` 再跑（本次实测都是先删后跑）。
13. **跨文件候选必然撞名，这一对等于没测。** 探针复制 A 的模块体、再 `open import B`；
    A、B 只要共享任何顶层名字（不必是这对本身同名，`swap-sends-0→1 ↔ flip-sends-0→1`
    就是因为两边都有 `C₀` 而撞），复制进来的那份就在模块体里报 `[ClashingDefinition]`。
    行号必然 ≤ `marker + 2`，旧版只看行号 → 误判 `NEQ`。实测（改版前）全仓 36 对里 25 对中招。
14. **限定名探针在这个库里不可用（已实测三次失败）。** 想把撞名绕开，两条路都堵死：
    - `open import M as A0` 仍然 unqualified 打开该模块，`_≈M_` 继续撞
      （`ClashingDefinition Multiple definitions of _≈M_. Previous definition at Base/MCorr.agda:90`）。
    - 换成纯限定 `import M as A0` 撞名消失，但 A 的类型文本里引用了模块**局部名**
      （`Base.MCorr` 的 `M`，不在顶层声明集合里），前缀覆盖不到 →
      `NotInScope: M (did you mean 'A0.M'?)`。
    - 退一步用 `chkT : <B 类型>; chkT = A0.<A 名>` 把 A 的**证明项**塞给 B 的类型：
      能编译到 `chkT` 处，但结论恒假——`A0.natToFin v != natToFin v`、`Obs !=< A0.Obs`，
      跨模块常量永远不同一。这条反而证明了 `CROSS_*` 分流是必需的设计（见 3.2）。
15. **`DECL` 只认"名字紧跟冒号"的顶格行，三类声明会被漏收。** 实测 ALMA 全仓需人工看
    的顶格行 200 条，其中真漏收的形态是：
    - 冒号后换行：`Base/MCorr.agda:228 compM :`（`:\s` 要求冒号后有空白）
    - 一行多名：`Physics/Quantum/Rotation.agda:159 rot0 rot1 : ...`
    - `mutual` 块内的缩进声明（6 个文件共 57 条）
    这三类会让 `decls`/候选数偏低，但不会造出假候选——影响是漏报，不是误报。
16. **定义体的边界必须是"下一个新声明行"，不是"下一个顶格行"（已修，曾让整档判据失效）。**
    Agda 的证明子句也是顶格的，三种写法：
    - 前缀名：`+interchange = medial +-0-commutativeMonoid`
    - **中缀名**：`m +ʳ zero = m`、`zero ⊔ n = n`（名字根本不在行首）
    - with 块：`foo x with y`、`... | z = ...`

    ⚠️ **这一条曾经让 `CROSS_COPY` / `CROSS_TYPE` 的区分完全失效**：旧边界按"顶格"截断，
    每条声明只取到类型行，于是"类型相同"自动等于"定义体相同"，`CROSS_TYPE` 恒为 0 条、
    `CROSS_COPY` 变成"类型相同"的同义词。实测（修前）：

    ```
    +interchange      body = '\x00NAME:∀abcd→(a+b)+(c+d)≡(a+c)+(b+d)'   ← 只有类型行
    +-four-rearrange  body = '\x00NAME:∀abcd→(a+b)+(c+d)≡(a+c)+(b+d)'   ← 一模一样
    ```

    两个证明体一个是一行 `medial`、一个是十行 `begin…end` 链，却被判"逐字相同"。
    现在边界换成 `is_decl_start()`：顶格且形如 `name :`（`DECL`）、`record/data/module`
    （`TOP`）、`{-#`、`open`/`import`，或有冒号无等号（覆盖一行多名）。修后同一对：

    ```
    +interchange      body = '\x00NAME:∀abcd→…+interchange=medial+-0-commutativeMonoid'
    +-four-rearrange  body = '\x00NAME:∀abcd→…+-four-rearrangeabcd=begin(a+b)+(c+d)≡⟨…'
    ```

    分类随之从 `CROSS_COPY` 变成 `CROSS_TYPE`/`CROSS_SCOPE`（全仓 `CROSS_COPY` 归 0）。
    代价：若某条声明的证明体里嵌了顶格 `{-# ... #-}` 块（非法写法），截取仍会提前断掉，
    属漏判方向。另外 `decl_body` 把声明名替换成 `\x00NAME` 时要替**全文**（早期只替第一处，
    名字只出现在定义行时两边形态不同，会把异名同证误判成 `CROSS_TYPE`——`swap-sends-0→1`
    ↔ `flip-sends-0→1` 就中过这一枪，已修）。
17. **块逐字相同不等于同一命题（狠狠踩过一次）。** 早期版本只比类型文本与定义体，
    把 `Poisson.agda` ↔ `Quadratic*.agda` 的 8 条判成"真重复、可直接合并"——实际两边
    `Obs` 分别是 3 字段与 6 字段，是两套不同的观测量代数，合并会直接改错语义。
    根因是类型文本里 `Obs` 被隐式推断掉了（`∀ f → bracket f f ≡ zero`），字面比对
    看不到任何区分信息。现在 `CROSS_SHAPE` 沿 `import` 追一跳比同名 `record` 字段列表；
    但只做 record 一层，若差异藏在普通定义的签名里（不是 record），仍会漏判。
18. **`{- ... -}` 块注释会造出幽灵声明（已修）。** 旧版只跳过 `--` 行注释与 `{-#` pragma，
    块注释里的顶格行会被当成真声明。实测样本：一个模块里放

    ```
    {- 块注释
    ghost : Set
    ghost = Set
    -}
    real : Set
    ```

    旧解析器返回 **2 条**（`ghost` + `real`），Agda 自己只认 1 条。危害比漏收更大：
    假声明会进候选表，还可能凑出「重复」。现在 `strip_block_comments()` 先把块注释
    换成空格（行号不动）再解析，`parse_file` / `records_of` / `decl_body` 都走这条路径，
    探针仍用原样源码（注释不该影响编译）。
    **ALMA 本库 244 个文件里没有一处跨行块注释，所以这条修复对本库的声明数没有影响
    （1991 前后一致）**，换到用块注释写文档的库才会显形。
19. **类型文本相同，不代表命题相同——`CROSS_SCOPE` 这一层是补上的。**
    类型里若没有类型标注（`∀ a b c d → (a + b) …`），量化域完全由运算符隐式决定。
    `+interchange` 与 `+-four-rearrange` 的类型文本逐字相同，但前者的 `+` 来自
    `Data.Rational`（ℚ）、后者来自 `Data.Nat.Base`（ℕ），是**两个不同定理**——这比
    `CROSS_SHAPE` 更隐蔽：后者至少还有同名 `record` 可追，前者连类型标注都没有。
    判据：解析两边 `open import M using (...)` / `renaming (...)` 的 form → 模块 映射，
    同一符号映射到不同模块即冲突。三条实现细节都踩过：
    - 列表分隔**三种都有**：`;`（ALMA 全库）、`,`、纯空白（stdlib 风格
      `using (ℕ zero suc _+_ _*_)`）。只按 `;` 切会整串当成一个名字，换库即漏。
    - `x as y`（using）与 `a to b`（renaming）取**右侧**：左侧是外部名，本文件里
      不叫这个。取左侧等于往映射里塞一个不存在的符号。
    - `using (a) renaming (a to b)` 本地只有 `b`，记 `a` 会把冲突判反。
    两道校准防止误伤：
    - 模块名前两段相同视同（`Data.Nat` ↔ `Data.Nat.Base` 是同一条 re-export 路径）；
    - `≡`/`ℕ`/`refl` 等基础名不可能有第二份实现，直接跳过。
    局限：re-export 只用"前两段"近似，vendor 深层 re-export 仍可能误报。
    `open import M public` 原先**故意不收**（名字无法逐一确定），代价是：一侧靠 public
    拿到 `+`、另一侧靠 `using` 拿到 `+` 时，public 侧查不到映射，`CROSS_SCOPE` 静默漏判。
    现在给了 `src_dirs` 就沿 public 链解析出**真正声明该名字的模块**（`_mod_origins`），
    所以 `Prelude public` 倒出来的 `_+_` 仍归 `Data.Nat.Base`，不会跟对侧误判成两个来源。
    实测对照（`audit/pub_t` 的 `PA`(public) / `PB`(using)）：
    ```
    旧（不传 src_dirs）: []
    新（传 src_dirs）  : ['+: Data.Rational.Base vs Data.Nat.Base']
    ```
    ALMA 全仓 34 对复跑**改判 0 条**——本库没有靠 public 拿到运算符的候选，这条是补漏，
    不是改结论。
20. **`_+_` 与 `+` 是同一个符号的两种写法，映射时必须都登记。** 类型里写的是
    `(a + b)`，`import` 列表里写的是 `_+_`。只按原名字比对，`+interchange` 那条
    永远命中不了（`_occurs('_+_', typ)` 在 `a + b` 上恒假）。`name_forms()` 用
    `re.findall(r'_([^_]+)_', n)` 抽出内层，`_+_ → {'_+_', '+'}`。
21. **判据算出来了，但没打印、没进 JSON（本轮真中过一次）。** `CROSS_SCOPE` 加进
    `t['status']` 之后只被汇总 `Counter` 统计到，明细打印的档位元组与 `cases[]` 的
    字段表都没加它，于是终端只显示一行总数、`+interchange` 那条不出现，
    `dedup_l1_*.json` 的 `cases[]` 里也没有 `scope_conflict`。**数字对、结论对、
    证据链断**——这类比算法错更隐蔽。
    修法：档位表提成模块级 `L1_STATUS_ORDER`，未登记的 status 会自动追加到末尾
    （新增档位不会再从明细里消失）；err 白名单改成"除 `DEFEQ`/`NEQ` 外都打"。
    复核方式固定为：`grep "### CROSS_SCOPE" 日志` + 断言 `all('scope_conflict' in c
    for c in cases)`。
22. **`err` 取"第一条 error"而不是末尾 400 字符（已改）。** 旧写法 `out[-400:]` 的问题是
    `.agda` 的错误按声明顺序报，模块体自己的错挂在 `chkT` 的错后面，而 `when checking`
    展开可能很长，会把真正的 `!=` 挤出窗口。实测对比（造一段 600 字符填充 + 一条错）：
    末尾 400 截出的第一行全是填充字符，`brief_error()` 截出的第一行是
    `Set != Set1`。找不到标准 `error:` 行时仍退回末尾 400。
23. **`shape_unresolved`：追 import 没追到 record 时不能说"没有结构冲突"（已改）。**
    `shape_conflicts` 里若 `find_record` 任一侧返回 `None`，旧代码直接跳过该名字，
    于是"没查到"和"结构一致"在结果上完全一样——漏判被伪装成通过。现在把两侧的解析
    状态记进 `t['shape_unresolved']`，进 JSON，终端也打 `⚠ record 未解析（本档可能不准）`。
    同时 `find_record` 的 `depth` 由 2 提到 4：stdlib 的 `Data.Rational → .Base → …`
    这类 re-export 链常超过两跳。ALMA 全仓 34 对实测**未解析 0 条**，说明 4 跳够用。
    注意"深度够不够"现在不再需要靠调参数保证：追不到会显式报出来，不会静默通过。
24. **探针名会与源文件自带同名定义相撞（已改成按实际名字避让）。** 追加一个同名的
    `chkT` 会得到 `[ClashingDefinition] Multiple definitions of chkT`（rc=42），
    `classify_l1` 见 `ClashingDefinition` 就归 `CLASH`，于是一对**本来相等**的声明被
    标成"跨文件撞名、这对没被测到"。实测（`audit/coll/E.agda` 自带 `chkT : Nat`）：
    ```
    chkT  ：rc=42  [ClashingDefinition] Multiple definitions of chkT  → CLASH
    chkT′ ：rc=0                                                      → DEFEQ
    ```
    但换成 `chkT′` 只解决一半：被测文件自己定义 `chkT′` 时照样撞（实测 `audit/coll2/Qp.agda`
    rc=42 `Multiple definitions of chkT′`）；更隐蔽的是 A 自己不写、但 `open import CH`
    把 `chkT′` 转出来（`audit/coll4` 实测同样 `Multiple definitions`）。现在
    `visible_names` 把「被测文件自己的声明 ∪ import 链上 depth 2 的模块声明」并成占用集，
    从 `chkT′` 起取第一个不在集合里、也不在文件文本里的名字，记在 `cases[].probe_name`。
    实测：`coll4`（A 经 import 拿到 `chkT′`）取到 `chkT′1` → `DEFEQ`；`coll3`（两边自带
    `chkT′`）→ `DEFEQ`；改前都是 `CLASH`。
    depth 2 只是"大概率不撞"，不是保证，所以还有一道**实测兜底**：`ClashingDefinition`
    的报错行若落在探针行上（≥ `marker`），说明撞的是**探针名**（不是 A/B 真同名——后者
    报在模块体里），此时换名重编，最多三次，`probe_retry` 记重试次数。实测
    `audit/coll5`（`A5 → CH1 → CH2 → CH3`，`chkT′` 在第三跳才出现、`visible_names` 看不到）：
    首次 `CLASH` → 重试取 `chkT′1` → `DEFEQ`。反向对照（`audit/coll6`：A6/B6 各自定义
    同一个 `lem`）：报错行 **7 < marker 11**，落在复制的模块体内，**不触发重试**，判
    `CLASH` 1 条——兜底不会把真同名洗成相等。
    **包模块不能替代避让**：`module _ where` 与 `module AuditProbe_<tag> where` 里的同名
    声明同样报 `Multiple definitions`（Agda 不允许在内层作用域重定义已 import 的名字），
    两种写法都实测过 `CLASH`。
    `′` 结尾是普通标识符；**不要**用 `_` 开头或结尾的名字。实测 `__audit_chkT_9f8a7__`
    直接 `ParseError: a name cannot contain two consecutive underscores`（单下划线开头
    则被当 mixfix 运算符，`chkT′ z = z` 这种写法不认）。所以"UUID 前缀探针名"这条路
    走不通——它不是撞不撞的问题，是名字根本写不进源码。
25. **块注释扫描必须识别字符串字面量（已改）。** Agda 里 `"{-"` 只是两个字符，不开注释；
    旧版逐字符看 `{-`/`-}`，遇到 `msg = "unterminated {- brace"` 会一直停在注释态，
    **把该行之后的所有声明抹掉**，而文件本身 `rc=0` 完全合法——静默整段丢失。实测：
    ```
    修复前：after : Nat / after = zero 全部消失
    修复后：after : Nat 保留，真正的 {- -} 仍被清成空格
    ```
    三类库实测都没有这种写法（ALMA 0 处、stdlib 0 处、categories 0 处），属潜伏缺陷。
    另：字符串里的 `--` 无害——行注释是**原样保留**的，截断后再拼回去仍是原文；
    stdlib 那 16 行 `"[--timing]"` 之类逐字未变。
26. **`OTHER` / `FAILED` 是混桶，不要再让它当黑箱（已补 `other_tag`）。** 同一个桶里混着
    三类完全不同的失败：探针本身不合法（`[SafeFlagPostulate]`，只在 `--safe` 下）、
    类型不匹配但不是定义不等（`[UnequalSorts]`）、元变量没解（`[UnsolvedMetaVariables]`）。
    现在每条失败都记首条错误的 `[标签]`（`cases[].other_tag`），终端也打
    `⚠ 未分类错误标签: [X]`；`status` 口径不变，所以历史计数可以直接对比。
    汇总行之后还打一行 `OTHER 错误分布: {标签: 条数}`，CI 日志不用逐条翻明细就能看出
    失败主因；出现 `SafeFlagPostulate` 时补一句「该库有 postulate/TrustMe，`--safe` 下
    探针不合法；去掉 `--safe` 才能判」，出现 `UnsolvedMetaVariables` 时补一句
    「源文件自己有未解元变量，探针会连带失败」。实测 `audit/pos_t`（含 `postulate ax`）：
    `--safe` 下 `OTHER 1` + `SafeFlagPostulate` + 提示；去掉 `--safe` 同一对直接 `DEFEQ`。

27. **`visible_names` 的两跳递归会重复打开同一模块，必须缓存解析结果。**
    从每个候选文件出发各走一次 import 链，同一模块被不同起点反复 `parse_module`
    + `module_imports`；不缓存时全仓 244 文件冷跑 **9.96 s**（名字累加 194451、热跑 0 s）。
    已按 `(路径, 相对名)` 缓存这两项：冷跑降到 **0.88 s**，峰值内存 39 MB。
    缓存键的上界就是仓库文件数，不做 LRU——淘汰只会把"再算一遍"请回来。

---

## 8. 推荐工作流

```bash
# 1) 提候选（秒级，随便跑）
agda-dedup scan --root . --out ./cands.json

# 2) 判真假（编译，只跑你关心的层；先 max-cases 验通路）
agda-dedup l1 --root . --filter /Real --jobs 3 \
        --max-cases 4 --out ./dedup_l1.json

# 3) 人工判读：DEFEQ 列表能合并的写进补丁，别名调用点改规范名；
#    跨文件按档位处理 —— CROSS_COPY(0) 是纯副本，可合并；
#    CROSS_TYPE(0) 是同题异证，也可合并；本库这两档都是空的
#    CROSS_SHAPE(8) 是同形不同义、CROSS_SCOPE(1) 是量化域不同，一律不合并；
#    CROSS_NAME(16) 不是重复

# 4) 对想删的条目做替换验证（一次一条，失败码指出卡在哪）
#    --cases 要指真实文件；先拿仓库样例跑通，再换成自己的
agda-dedup l2 --root . --cases tools/agda-dedup/l2_cases_example.json --jobs 2

# 5) 改完必回归
cd <repo> && agda -i src --double-check src/Everything.agda
```

第 3 步和第 4 步是**人**的活：工具只给 `DEFEQ`/`REPLACED`，删不删、留不留由判读决定
（排版重复删掉不减少定理量，真重复才值得动源码）。

---

## 9. 这次没做的

- `l1` 的 `DEFEQ` 分支只有历史证据（合并前判出 12 组 DEFEQ、落地 6 组），
  当前提交上跑出来是 0 条，没有在现状上重新构造一对等价声明来复验这条通路。
- `CROSS_COPY` / `CROSS_TYPE` 现在都是 **0 条**；仍在库里的
  `+interchange` 属 `CROSS_SCOPE`：类型文本与 `+-four-rearrange` 一字不差，但 `_+_`
  一个来自 ℚ、一个来自 ℕ，**不是同一命题，不该合并**。这条判据是本轮新加的，
  所以"3 条真重复"这个早期说法彻底作废（2 条已合并且正确，1 条不该合）。
  已合并的两条（`toℕ-natToFin`、`swap-sends-*`）用 `git show d72d569^` 取旧文件复验：
  `typ same=True`、`body same=True`、`scope=[]`，确属纯副本；合并后三个改动文件各自
  `--double-check` 均为 `rc=0`。
- `CROSS_SHAPE` 只比了 `record`/`data` 这一层字段列表，`CROSS_SCOPE` 只比了显式
  `using` 导入。差异若藏在普通定义的签名里（两处同名但类型不同的辅助函数，且名字都
  来自同一个模块），两档都看不出来，仍会落到 `CROSS_TYPE`/`CROSS_COPY`。
- `cross` 没有对 `SketchPass`/`Physics` 这些自造层单独调 vocab 判据，
  304/331 这个"纯共享词汇"数在不同层上口径一致但没分层验证。
- `l2` 只验了 4 条已实证的用例；上一轮那 7 条未跑候选（`rev-tri`、`abs-lip`、
  `neg-abs`、`sub-cancel`、`*-mono-≤-nonNeg`、`x<x+1` 等）的卡点仍是人工结论，
  工具没有自动给出"缺哪个引理"的能力。
- 探针侧仍有 3 条历史诊断分支（`CLASH`/`SCOPE_ERROR`/`OTHER`）只在
  `--cross-file try` 下才会出现，其代码路径已实测（25 条 CLASH 记录），但不再默认走到。

**评估过但没做的七件（附实测理由，不是"懒得做"）**

1. **不解析 `where` / `record` / `let` 内部的缩进声明，只收 `module _` 块体的同级声明。**
   按块语境拆开：`module _` 体内 492（ALMA）、record 字段、`where` 局部辅助、`let`/`instance`
   内部绑定——只有第一类算"与顶格声明同级"。把这 492 条按现有 `shape` 逻辑全收进来模拟过
   一遍：候选声明 1247 → **3657**（2.9 倍），形状配对 34 → **47**（只多 13 对），且新增的
   39 条同名对里第一条就是 `(t @ Cosmos/Carried/DetColimit.agda:37` —— `(t : ...) → ...`
   里的绑定名被 `DECL` 当成了声明名，一批垃圾名进候选表。
   代价是候选洪水 + 系统性假名，收益 13 对里还没有一条被验证是真重复。**所以不按 `shape`
   收**（这条仍是"不做"）。现在的做法是只按「类型文本归一后完全相同」配对，走文本档
   `CROSS_COPY` / `CROSS_TYPE`，实测 ALMA 多 1 对、agda-categories 多 5 对。
   **但要记住这不是"Agda 不允许"**：缩进模块体合法（实测 `rc=0`），只是本工具原先不收。
   在缩进风格的库上覆盖率会掉——`agda-categories-0.3.0` 实测顶格 933 条、
   `module _` 体内 **560 条**，**覆盖 74%**（早先那个"只覆盖 19%"是把 record 字段和
   `let`/`where` 局部绑定也算进了分母；"42%"则是把块头续行和 `private` 里层算错了）。
   现在 `scan`/`l1` 遇 `module _` 体内声明超过顶格 10% 会打一行 `note:` 提示。
2. **不改 `shape` 的内部表示。** 全仓 `scan` 实测冷跑 1.34 s、热跑 **0.65 s**（244 文件
   / 1991 声明）。整个形状分组阶段本来就占不到一秒，而 `l1` 是分钟级（编译）。瓶颈在
   Agda 不在正则，换结构化表示没有收益。
3. **不拆 JSON 的 `cases`。** `declarations` 与 `audit_results` 分开确实更干净，但现有
   所有消费方（`dump_l1.py` 一类脚本、报告生成）都读 `cases`，改结构要连带改一圈，
   收益是"下游友好"，而下游目前就是我自己。等真有第二个消费方再说。
4. **不加磁盘解析缓存。** 同一个理由的反面：`_src_cache` 只在进程内生效，跨运行不复用，
   但解析全程只有 ~0.6 s（scan 热跑 0.65 s 的绝大部分），而 `l1` 一轮是分钟级、时间全
   在 Agda 编译上。给解析加文件 hash 磁盘缓存，最多省半秒，收益 <1%，还要引入缓存
   失效与脏读的新风险。真嫌慢应该减探针数量，不是缓存正则。
5. **不自动生成 L2 用例。** `l1`/`cross` 的结果里只有**本库**的名字与类型文本，凑一条
   `{file, name, imports, clause, rhs}` 还缺两样关键信息：目标定理叫什么、它的 import
   路径怎么写。这两个从本库结果推不出来，只能猜；猜错就产出一批假 `REPLACED`，
   比手工写更危险。`l2` 缺的是"人指定替换目标"这一步，不是模板。
6. **不产出 HTML 报告，也不加 `--md`。** 结果全在 JSON 与终端里，二次加工是自由的；
   做成 HTML 要加一层模板渲染与样式维护，而"点击跳源码"只能给 `file://` 链接——浏览器
   默认拦截本地路径跳转，跨盘更不行，实际点不动。`--md` 同理：Markdown 表格里的相对路径
   在 PR 评论、CI 页面里都不是可点的链接，要真能跳就必须再引入 `--repo-url` 参数拼
   `https://github.com/<org>/<repo>/blob/<sha>/<path>#L<n>`，而那意味着工具要知道远端仓库
   与提交号——这份信息不在源码里，猜出来就会给出一批 404 链接。JSON 已有全部字段，
   需要什么渲染交给下游。顺带更正一条常见前提：本工具**从未**产出过"HTML 依赖图"，
   工作目录里没有任何 `.html` 文件，这类建议是按想象的历史提的。
   耗时统计则**已做**：`report.elapsed` + 终端一行 `耗时 X.XX s`（见第 4 节）。
7. **不把 `--jobs` 改成自适应。** 本机 `nproc=12`、内存 **7 GB**；`min(8, cpu_count())`
   恰好在测评机取到 8，而冷缓存 8 路 Agda 编译实测 load 13、机器压满（两次中止，
   `ls` 都排不上）。默认 4 是刻意上限，不是"没考虑自适应"——真要自适应应当往下取
   （如 `min(4, cores//3)`），而不是往上顶到 8。
8. **不用 `--interaction` / `--html` / tree-sitter 去取真 AST。**
   `--interaction` 是 Emacs 交互模式的 REPL 协议（`--help` 原文 "for use with the Emacs
   mode"），没有"导出声明列表"的指令；`--html` 只是**高亮源码**——实测 `U2.html` 是
   `<pre class="Agda">` 里逐 token 的 `<a>` 锚点，仍是同一份文本，从中取声明还是要正则，
   而且它要求整文件通过类型检查（`scan` 0.5 s 会变成全库编译）。`tree-sitter-agda` 是外部
   依赖，与本工具"只用标准库、单文件可拷走"的前提冲突。真要结构化 AST 得换整个解析层，
   收益是"缩进模块体也能收"，代价是部署形态从"拷一个 .py"变成"装一套工具链"。
   缩进覆盖率的损失已用 `note:` 告警显式暴露（见第 9 节第 1 条），不静默。

