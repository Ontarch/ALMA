#!/usr/bin/env python3
import re
import subprocess
import sys
import os

def filter_and_generate(in_file, out_dot, prefixes, out_html):
    nodes = {}
    edges = []
    node_re = re.compile(r'\s*(m\d+)\[label="([^"]+)"\];')
    edge_re = re.compile(r'\s*(m\d+)\s*->\s*(m\d+);')
    
    with open(in_file) as f:
        for line in f:
            m = node_re.match(line)
            if m:
                nodes[m.group(1)] = m.group(2)
                continue
            m = edge_re.match(line)
            if m:
                edges.append((m.group(1), m.group(2)))
                
    keep = {i for i, name in nodes.items() if any(name.startswith(p) for p in prefixes)}
    kept_edges = [(a, b) for a, b in edges if a in keep and b in keep]
    
    with open(out_dot, 'w') as f:
        f.write('digraph dependencies {\n')
        for i, name in nodes.items():
            if i in keep:
                f.write(f'   {i}[label="{name}"];\n')
        for a, b in kept_edges:
            f.write(f'   {a} -> {b};\n')
        f.write('}\n')
    
    script_dir = os.path.dirname(os.path.abspath(__file__))
    dot_to_html_path = os.path.join(script_dir, 'dot_to_html.py')
    
    subprocess.run(['python3', dot_to_html_path, out_dot, out_html], check=True)

if __name__ == '__main__':
    project_prefixes = ('Base', 'Cosmos', 'Equivalence', 'Physics', 'Real', 'SecondPass', 'SketchPass', 'Wellspring', 'Everything')
    filter_and_generate('src/deps.dot', 'deps-project.dot', project_prefixes, 'deps-project.html')

    real_prefixes = ('Real',)
    filter_and_generate('src/deps.dot', 'deps-real.dot', real_prefixes, 'deps-real.html')
