import re
import sys

INCLUDE_PREFIXES = (
    'Base.', 'Cosmos.', 'Equivalence.', 'Physics.',
    'Real.', 'SecondPass.', 'SketchPass.', 'Wellspring.',
    'Everything',
)

def included(name):
    return any(name.startswith(p) for p in INCLUDE_PREFIXES)

node_re = re.compile(r'\s*(m\d+)\[label="([^"]+)"\];')
edge_re = re.compile(r'\s*(m\d+)\s*->\s*(m\d+);')

inp = sys.argv[1] if len(sys.argv) > 1 else 'deps.dot'
out = sys.argv[2] if len(sys.argv) > 2 else 'deps-project.dot'

nodes = {}
edges = []
with open(inp) as f:
    for line in f:
        m = node_re.match(line)
        if m:
            nodes[m.group(1)] = m.group(2)
            continue
        m = edge_re.match(line)
        if m:
            edges.append((m.group(1), m.group(2)))

keep = {i for i, name in nodes.items() if included(name)}
kept_edges = [(a, b) for a, b in edges if a in keep and b in keep]

with open(out, 'w') as f:
    f.write('digraph dependencies {\n')
    for i, name in nodes.items():
        if i in keep:
            f.write(f'   {i}[label="{name}"];\n')
    for a, b in kept_edges:
        f.write(f'   {a} -> {b};\n')
    f.write('}\n')

print(f'kept {len(keep)} / {len(nodes)} nodes, '
      f'{len(kept_edges)} / {len(edges)} edges')
