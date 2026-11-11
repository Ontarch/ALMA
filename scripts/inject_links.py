#!/usr/bin/env python3
import os
import re

def get_node_count(filepath):
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
            m = re.search(r'Nodes:\s*(\d+)', content)
            if m: return m.group(1)
    except Exception:
        pass
    return "?"

def main():
    index_path = './docs/index.html'
    if not os.path.exists(index_path):
        print("Error: ./docs/index.html not found!")
        return

    proj_nodes = get_node_count('deps-project.html')
    real_nodes = get_node_count('deps-real.html')

    with open(index_path, 'r', encoding='utf-8') as f:
        content = f.read()

    injected_html = (
        "<br>"
        "<span style='font-family: monospace; color: #6a737d;'>-- Interactive Graphs:</span><br>"
        "&nbsp;&nbsp;"
        "<a href='deps-project.html' target='_blank' style='display: inline; font-family: monospace; font-size: inherit; color: #0366d6; text-decoration: none; font-weight: 600;'>Full Project (" + str(proj_nodes) + " nodes)</a>"
        "<span style='color: #d1d5da; margin: 0 4px;'>|</span>"
        "<a href='deps-real.html' target='_blank' style='display: inline; font-family: monospace; font-size: inherit; color: #28a745; text-decoration: none; font-weight: 600;'>Real Module (" + str(real_nodes) + " nodes)</a>"
        "<br>"
    )
    
    pattern = r'(<a\s+[^>]*href="Everything\.html"[^>]*>Everything</a>)\s*'
    
    if re.search(pattern, content):
        content = re.sub(pattern, r'\1' + injected_html, content, count=1)
        print("Injected after 'Everything' link.")
    else:
        target_text = 'import Everything'
        if target_text in content:
            content = content.replace(target_text, target_text + injected_html, 1)
            print("Injected after text 'import Everything'.")
        else:
            target_all = '-- All modules'
            if target_all in content:
                content = content.replace(target_all, injected_html + target_all, 1)
                print("Injected before '-- All modules'.")
            else:
                print("Warning: Could not find insertion point.")

    with open(index_path, 'w', encoding='utf-8') as f:
        f.write(content)

if __name__ == '__main__':
    main()
