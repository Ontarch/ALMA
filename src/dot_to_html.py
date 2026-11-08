import re, json, sys

def parse_dot(filename):
    nodes, edges = {}, []
    node_re = re.compile(r'\s*(m\d+)\[label="([^"]+)"\];')
    edge_re = re.compile(r'\s*(m\d+)\s*->\s*(m\d+);')
    with open(filename) as f:
        for line in f:
            m = node_re.match(line)
            if m: 
                nodes[m.group(1)] = m.group(2)
                continue
            m = edge_re.match(line)
            if m: 
                edges.append((m.group(1), m.group(2)))
    return nodes, edges

def make_html(nodes, edges, output):
    data_nodes = [{"id": k, "label": v} for k, v in nodes.items()]
    data_edges = [{"source": a, "target": b} for a, b in edges]

    html = f"""<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<title>Agda Dependencies</title>
<style>
  body {{ margin:0; font-family:monospace; background:#f4f5f7; overflow:hidden; user-select:none; }}
  #search {{ position:absolute; top:15px; left:15px; z-index:100; padding:8px 12px; border:1px solid #ccc; border-radius:4px; width:300px; font-size:14px; box-shadow: 0 2px 5px rgba(0,0,0,0.1); }}
  #viewport {{ position:absolute; top:0; left:0; transform-origin: 0 0; cursor:grab; }}
  #viewport:active {{ cursor:grabbing; }}
  
  .node {{ position:absolute; padding:6px 10px; background:#fff; border:1.5px solid #6c757d; border-radius:16px; font-size:12px; cursor:pointer; transform:translate(-50%, -50%); white-space:nowrap; box-shadow: 0 2px 4px rgba(0,0,0,0.05); transition: background 0.2s, border-color 0.2s, opacity 0.2s; z-index:2; }}
  .node:hover {{ border-color: #007bff; box-shadow: 0 4px 8px rgba(0,123,255,0.2); }}
  .node.highlight {{ background:#ffe066; border-color:#f59f00; font-weight:bold; z-index:10; box-shadow: 0 0 10px rgba(245,159,0,0.5); }}
  .node.faded {{ opacity: 0.1; }}
  
  svg {{ position:absolute; top:0; left:0; pointer-events:none; z-index:1; }}
  path {{ stroke:#aeb5bc; stroke-width:1.5; transition: stroke 0.2s; }}
  path.highlight {{ stroke:#f59f00; stroke-width:2.5; }}
  
  #info {{ position:absolute; bottom:15px; right:15px; background:#fff; padding:6px 10px; border-radius:4px; font-size:12px; border:1px solid #ddd; box-shadow: 0 2px 5px rgba(0,0,0,0.1); z-index: 100; }}
</style>
</head>
<body>
<input id="search" placeholder="Search module...">
<div id="viewport">
  <svg id="lines">
    <defs>
      <marker id="arrow" viewBox="0 0 10 10" refX="10" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
        <path d="M 0 0 L 10 5 L 0 10 z" fill="#aeb5bc" />
      </marker>
      <marker id="arrow-hl" viewBox="0 0 10 10" refX="10" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
        <path d="M 0 0 L 10 5 L 0 10 z" fill="#f59f00" />
      </marker>
    </defs>
  </svg>
  <div id="nodes-container"></div>
</div>
<div id="info">Nodes: {len(nodes)} | Edges: {len(edges)}<br><small>点击节点高亮上下游 | 拖拽平移 | 滚轮缩放</small></div>

<script>
  const nodesData = {json.dumps(data_nodes)};
  const edgesData = {json.dumps(data_edges)};

  const viewport = document.getElementById('viewport');
  const container = document.getElementById('nodes-container');
  const svg = document.getElementById('lines');
  const nodeElements = {{}};
  const nodeDims = {{}};

  // 1. 初始化节点
  nodesData.forEach((n) => {{
    const div = document.createElement('div');
    div.className = 'node';
    div.id = 'node-' + n.id;
    div.textContent = n.label;
    container.appendChild(div);
    nodeElements[n.id] = div;
  }});

  nodesData.forEach((n, i) => {{
    const rect = nodeElements[n.id].getBoundingClientRect();
    nodeDims[n.id] = {{ w: rect.width, h: rect.height }};
    n.x = (Math.random() - 0.5) * 2000;
    n.y = (Math.random() - 0.5) * 2000;
    n.vx = 0; n.vy = 0;
  }});

  // 2. 物理引擎
  const MAX_COORD = 5000;
  for (let iter = 0; iter < 300; iter++) {{
    for (let i = 0; i < nodesData.length; i++) {{
      for (let j = i + 1; j < nodesData.length; j++) {{
        const n1 = nodesData[i], n2 = nodesData[j];
        let dx = n2.x - n1.x;
        let dy = n2.y - n1.y;
        let distSq = dx*dx + dy*dy;
        if (distSq === 0) distSq = 0.1;
        let dist = Math.sqrt(distSq);
        
        if (dist < 1000) {{
          let force = 30000 / distSq; 
          let fx = (dx / dist) * force;
          let fy = (dy / dist) * force;
          n1.vx -= fx; n1.vy -= fy;
          n2.vx += fx; n2.vy += fy;
        }}
      }}
    }}

    edgesData.forEach(e => {{
      const n1 = nodesData.find(n => n.id === e.source);
      const n2 = nodesData.find(n => n.id === e.target);
      let dx = n2.x - n1.x;
      let dy = n2.y - n1.y;
      let dist = Math.sqrt(dx*dx + dy*dy) || 0.1;
      
      let targetDist = 300; 
      let force = (dist - targetDist) * 0.03;
      
      let fx = (dx / dist) * force;
      let fy = (dy / dist) * force;
      
      n1.vx += fx; n1.vy += fy;
      n2.vx -= fx; n2.vy -= fy;
    }});

    nodesData.forEach(n => {{
      n.vx -= n.x * 0.01;
      n.vy -= n.y * 0.01;
      n.vx *= 0.8; n.vy *= 0.8;
      
      n.vx = Math.max(-20, Math.min(20, n.vx));
      n.vy = Math.max(-20, Math.min(20, n.vy));
      
      n.x += n.vx; n.y += n.vy;
      
      if (n.x > MAX_COORD) n.x = MAX_COORD;
      if (n.x < -MAX_COORD) n.x = -MAX_COORD;
      if (n.y > MAX_COORD) n.y = MAX_COORD;
      if (n.y < -MAX_COORD) n.y = -MAX_COORD;
    }});
  }}

  // 3. 坐标平移与边界计算
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  nodesData.forEach(n => {{
    minX = Math.min(minX, n.x); minY = Math.min(minY, n.y);
    maxX = Math.max(maxX, n.x); maxY = Math.max(maxY, n.y);
  }});

  const padding = 500;
  const offsetX = -minX + padding;
  const offsetY = -minY + padding;
  const totalWidth = maxX - minX + padding * 2;
  const totalHeight = maxY - minY + padding * 2;

  viewport.style.width = totalWidth + 'px';
  viewport.style.height = totalHeight + 'px';
  svg.setAttribute('width', totalWidth);
  svg.setAttribute('height', totalHeight);

  nodesData.forEach(n => {{
    n.x += offsetX; n.y += offsetY;
    nodeElements[n.id].style.left = n.x + 'px';
    nodeElements[n.id].style.top = n.y + 'px';
  }});

  // 4. 绘制曲线连线
  edgesData.forEach(e => {{
    const n1 = nodesData.find(n => n.id === e.source);
    const n2 = nodesData.find(n => n.id === e.target);
    const d1 = nodeDims[e.source];
    const d2 = nodeDims[e.target];
    
    const angle = Math.atan2(n2.y - n1.y, n2.x - n1.x);
    const r1x = (d1.w / 2) + 2; const r1y = (d1.h / 2) + 2;
    const r2x = (d2.w / 2) + 8; const r2y = (d2.h / 2) + 8;

    const x1 = n1.x + Math.cos(angle) * r1x;
    const y1 = n1.y + Math.sin(angle) * r1y;
    const x2 = n2.x - Math.cos(angle) * r2x;
    const y2 = n2.y - Math.sin(angle) * r2y;

    const cx = (x1 + x2) / 2 - (y2 - y1) / 8;
    const cy = (y1 + y2) / 2 + (x2 - x1) / 8;
    const d = `M ${{x1}} ${{y1}} Q ${{cx}} ${{cy}} ${{x2}} ${{y2}}`;

    const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
    path.setAttribute('d', d);
    path.setAttribute('fill', 'none');
    path.setAttribute('marker-end', 'url(#arrow)');
    path.id = `path-${{e.source}}-${{e.target}}`;
    svg.appendChild(path);
  }});

  // 5. 视图初始化与缩放核心逻辑 (修复了偏移问题)
  let scale = Math.min(window.innerWidth / totalWidth, window.innerHeight / totalHeight) * 0.9;
  scale = Math.min(Math.max(scale, 0.05), 1.0);
  
  // 让图的中心对齐到屏幕中心
  let translateX = (window.innerWidth - totalWidth * scale) / 2;
  let translateY = (window.innerHeight - totalHeight * scale) / 2;

  const updateTransform = () => {{
    viewport.style.transform = `translate(${{translateX}}px, ${{translateY}}px) scale(${{scale}})`;
  }};
  updateTransform();

  let isDragging = false;
  let startX, startY;

  document.addEventListener('mousedown', (e) => {{
    if (e.target.closest('.node') || e.target.id === 'search') return;
    isDragging = true;
    startX = e.clientX - translateX;
    startY = e.clientY - translateY;
    clearHighlight();
  }});

  document.addEventListener('mousemove', (e) => {{
    if (!isDragging) return;
    translateX = e.clientX - startX;
    translateY = e.clientY - startY;
    updateTransform();
  }});

  document.addEventListener('mouseup', () => isDragging = false);

  // 修复缩放中心点定位的数学公式
  document.addEventListener('wheel', (e) => {{
    if (e.ctrlKey) return;
    e.preventDefault();
    
    const oldScale = scale;
    const zoomSensitivity = 0.001;
    scale -= e.deltaY * zoomSensitivity;
    scale = Math.min(Math.max(0.02, scale), 3); // 限制范围
    
    // 鼠标当前位置的屏幕坐标
    const mouseX = e.clientX;
    const mouseY = e.clientY;
    
    // 核心公式：确保鼠标指向的视口位置在缩放前后不变
    translateX = mouseX - (mouseX - translateX) * (scale / oldScale);
    translateY = mouseY - (mouseY - translateY) * (scale / oldScale);
    
    updateTransform();
  }}, {{ passive: false }});

  // 6. 高亮交互
  function clearHighlight() {{
    document.querySelectorAll('.node').forEach(el => el.className = 'node');
    document.querySelectorAll('path').forEach(el => {{
      el.style.display = 'block';
      el.classList.remove('highlight');
      el.setAttribute('marker-end', 'url(#arrow)');
    }});
  }}

  let selectedNodeId = null;

  function highlightNode(nodeId) {{
    if (selectedNodeId === nodeId) {{
      selectedNodeId = null;
      clearHighlight();
      return;
    }}
    selectedNodeId = nodeId;
    clearHighlight();

    const neighbors = new Set();
    neighbors.add(nodeId);
    edgesData.forEach(e => {{
      if (e.source === nodeId) neighbors.add(e.target);
      if (e.target === nodeId) neighbors.add(e.source);
    }});

    nodesData.forEach(n => {{
      if (neighbors.has(n.id)) nodeElements[n.id].classList.add('highlight');
      else nodeElements[n.id].classList.add('faded');
    }});

    edgesData.forEach(e => {{
      const path = document.getElementById(`path-${{e.source}}-${{e.target}}`);
      if (e.source === nodeId || e.target === nodeId) {{
        path.classList.add('highlight');
        path.setAttribute('marker-end', 'url(#arrow-hl)');
      }} else {{
        path.style.display = 'none';
      }}
    }});
  }}

  nodesData.forEach(n => {{
    nodeElements[n.id].addEventListener('click', (e) => {{
      e.stopPropagation();
      highlightNode(n.id);
    }});
  }});

  // 7. 搜索
  document.getElementById('search').addEventListener('input', (e) => {{
    const q = e.target.value.toLowerCase().trim();
    if (!q) {{
      clearHighlight();
      return;
    }}
    
    const matched = new Set();
    nodesData.forEach(n => {{
      if (n.label.toLowerCase().includes(q)) matched.add(n.id);
    }});

    clearHighlight();

    nodesData.forEach(n => {{
      if (matched.has(n.id)) nodeElements[n.id].classList.add('highlight');
      else nodeElements[n.id].classList.add('faded');
    }});

    edgesData.forEach(e => {{
      const path = document.getElementById(`path-${{e.source}}-${{e.target}}`);
      if (matched.has(e.source) && matched.has(e.target)) {{
        path.classList.add('highlight');
        path.setAttribute('marker-end', 'url(#arrow-hl)');
      }} else {{
        path.style.display = 'none';
      }}
    }});
  }});
</script>
</body>
</html>"""
    with open(output, 'w') as f: 
        f.write(html)
    print(f'Generated {output}: {len(nodes)} nodes, {len(edges)} edges')

if __name__ == '__main__':
    inp = sys.argv[1] if len(sys.argv) > 1 else 'deps-project.dot'
    out = sys.argv[2] if len(sys.argv) > 2 else 'deps-project.html'
    make_html(*parse_dot(inp), out)
