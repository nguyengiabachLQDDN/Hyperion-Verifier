// language: TypeScript, file: web/src/app.ts, target: Browser ES Module
// Giao diện Web Studio HYPERION (100% tiếng Việt): SSE Telemetry, Đồ thị CFG/UNSAT/Tua vết, Sinh Unit Test, Kiểm chứng Tương đương & Diệt Mutant SMT

                          
             
                
                     
                         
                    
                   
                          
                   
                    
                      
               
                    
                       
             
             
 

                          
                 
                 
               
                    
 

                           
                   
                   
                                
                     
                   
                   
                                                  
                                                               
 

                            
               
                   
                      
               
                      
                                
                                    
                
 

                        
             
                    
                        
 

const SAMPLE_PY = `def audit_packet_gateway(user_input, header_len, mode):
    buf = [10, 20, 30, 40, 50, 60]
    token = read_packet(user_input)
    acc = (header_len ^ 19) + 4
    if header_len > 30 and header_len < 10:
        return -999
    if mode == 7 and header_len >= 6:
        val = buf[header_len]
        acc = acc + val
    if mode < 0:
        sql_query(token, acc)
    denom = mode - 3
    if header_len > 12:
        acc = acc // denom
    assert acc >= 0, "gateway_acc_non_negative"
    return acc
`;

const SAMPLE_TS = `export function verifySessionFrame(frameLen: number, flags: number, slot: number, untrustedPayload: number): number {
    let slots = [1, 2, 3, 4];
    let sig = (frameLen ^ 29) + (flags & 15);
    if (flags > 20 && flags < 5) {
        return -1;
    }
    if (flags == 5 && slot >= 4) {
        let bad = slots[slot];
        sig = sig + bad;
    }
    if (frameLen == 21 && flags < 0) {
        sqlExec(untrustedPayload, sig);
    }
    assert(sig > -100, "sig_invariant");
    return sig;
}
`;

const SAMPLE_EQUIV_OLD_PY = `def tinh_phi_truy_cap(role, amount, coupon):
    if role <= 0:
        return -1
    fee = amount * 2
    if role == 2:
        fee = fee - coupon
    else:
        if coupon > 10:
            fee = fee - 10
        else:
            fee = fee - coupon
    if fee < 0:
        return 0
    return fee
`;

const SAMPLE_EQUIV_NEW_PY = `def tinh_phi_moi(role, amount, coupon):
    if role <= 0:
        return -1
    discount = coupon
    if role != 2 and coupon > 10:
        discount = 10
    fee = amount * 2 - discount
    if fee < 0:
        return 0
    return fee
`;

const $ =                        (id        )    => document.getElementById(id)     ;

                         
               
                    
              
              
              
              
                         
                      
                       
                      
                      
                     
                     
                    
                        
                        
                            
                         
                             
                        
                            
                        
                            
                        
                            
                          
                              
                                
                  
                     
                         
 

function getCanvasPalette()                {
  const isLight = document.documentElement.dataset.theme === "light";
  if (isLight) {
    return {
      grid: "#e4e1d6",
      axisLabel: "#6e6b62",
      cpu: "#c96442",
      ram: "#5f7247",
      smt: "#4e7ca8",
      mut: "#6e6b62",
      cfgEdgeDefault: "#6e6b62",
      cfgEdgeTrue: "#5f7247",
      cfgEdgeFalse: "#b57918",
      cfgEdgeBack: "#c96442",
      cfgEdgeDead: "#c04134",
      cfgEdgeDom: "rgba(78, 124, 168, 0.5)",
      cfgEdgeDfg: "rgba(201, 100, 66, 0.42)",
      cfgNodeBg: "#ffffff",
      cfgNodeBorder: "#c9c5b6",
      cfgNodeDeadBg: "#fbeceb",
      cfgNodeDeadBorder: "#c04134",
      cfgNodeEntryBg: "#edf3f8",
      cfgNodeEntryBorder: "#4e7ca8",
      cfgNodeSinkBg: "#faeee9",
      cfgNodeSinkBorder: "#c96442",
      cfgNodeLoopBg: "#faf4e6",
      cfgNodeLoopBorder: "#b57918",
      cfgNodeExitBg: "#eef3ea",
      cfgNodeExitBorder: "#5f7247",
      cfgNodeReplayBg: "#e3edf6",
      cfgNodeReplayBorder: "#4e7ca8",
      cfgNodeSelectedBorder: "#c96442",
      cfgText: "#141413",
      cfgSubText: "#5e5c54",
      cfgDeadSubText: "#a83428",
    };
  }
  return {
    grid: "#2a2824",
    axisLabel: "#7c7a72",
    cpu: "#d97757",
    ram: "#788c5d",
    smt: "#6a9bcc",
    mut: "#b0aea5",
    cfgEdgeDefault: "#7a7870",
    cfgEdgeTrue: "#788c5d",
    cfgEdgeFalse: "#e0a448",
    cfgEdgeBack: "#d97757",
    cfgEdgeDead: "#d95d4e",
    cfgEdgeDom: "rgba(106, 155, 204, 0.5)",
    cfgEdgeDfg: "rgba(217, 119, 87, 0.42)",
    cfgNodeBg: "#1c1b19",
    cfgNodeBorder: "#423f38",
    cfgNodeDeadBg: "#2b1815",
    cfgNodeDeadBorder: "#d95d4e",
    cfgNodeEntryBg: "#172330",
    cfgNodeEntryBorder: "#6a9bcc",
    cfgNodeSinkBg: "#2c1b16",
    cfgNodeSinkBorder: "#d97757",
    cfgNodeLoopBg: "#28231a",
    cfgNodeLoopBorder: "#e0a448",
    cfgNodeExitBg: "#1c2419",
    cfgNodeExitBorder: "#788c5d",
    cfgNodeReplayBg: "#1e2d3d",
    cfgNodeReplayBorder: "#6a9bcc",
    cfgNodeSelectedBorder: "#d97757",
    cfgText: "#faf9f5",
    cfgSubText: "#b0aea5",
    cfgDeadSubText: "#f0998d",
  };
}

class CfgRenderer {
          canvas                   ;
          ctx                          ;
          graph                  = null;
          selectedId                = null;
          activeReplayBlockId                = null;
          dragNode                 = null;
          panning = false;
          panX = 40;
          panY = 30;
          zoom = 1.0;
          lastMouse = { x: 0, y: 0 };
         showDead = true;
         showDom = true;
         showDfg = true;

          animFrameId                = null;

  constructor(canvas                   ) {
    this.canvas = canvas;
    this.ctx = canvas.getContext("2d") ;
    this.bindEvents();
  }

         setGraph(g                 )       {
    this.graph = g;
    this.selectedId = null;
    this.activeReplayBlockId = null;
    if (g) {
      this.layoutGraph(g);
      this.startLoop();
    } else {
      this.drawFrame();
    }
  }

          startLoop()       {
    if (this.animFrameId === null) {
      this.animFrameId = requestAnimationFrame(this.animate);
    }
  }

         setActiveReplayBlock(blockId               )       {
    this.activeReplayBlockId = blockId;
    this.drawFrame();
  }

         redraw()       {
    this.drawFrame();
  }

         resetLayout()       {
    if (!this.graph) return;
    this.panX = 40;
    this.panY = 30;
    this.zoom = 1.0;
    this.layoutGraph(this.graph);
    this.drawFrame();
  }

          layoutGraph(g          )       {
    const w = this.canvas.width || 800;
    const cols = Math.max(2, Math.ceil(Math.sqrt(g.nodes.length)));
    g.nodes.forEach((n, idx) => {
      const row = Math.floor(idx / cols);
      const col = idx % cols;
      n.x = 120 + col * 210 + (row % 2) * 45;
      n.y = 80 + row * 125;
    });
    if (g.nodes.length > 0 && w > 0) {
      this.panX = Math.max(20, (w - cols * 210) / 2);
    }
  }

          toWorld(sx        , sy        )                           {
    return { x: (sx - this.panX) / this.zoom, y: (sy - this.panY) / this.zoom };
  }

          bindEvents()       {
    this.canvas.addEventListener("mousedown", (e) => {
      const rect = this.canvas.getBoundingClientRect();
      const sx = e.clientX - rect.left;
      const sy = e.clientY - rect.top;
      this.lastMouse = { x: sx, y: sy };
      const pt = this.toWorld(sx, sy);

      if (this.graph) {
        for (const n of this.graph.nodes) {
          if (Math.abs(pt.x - (n.x ?? 0)) < 78 && Math.abs(pt.y - (n.y ?? 0)) < 28) {
            this.dragNode = n;
            this.selectedId = n.id;
            this.updateOverlay(n);
            return;
          }
        }
      }
      this.panning = true;
    });

    window.addEventListener("mousemove", (e) => {
      if (!this.dragNode && !this.panning) return;
      const rect = this.canvas.getBoundingClientRect();
      const sx = e.clientX - rect.left;
      const sy = e.clientY - rect.top;
      if (this.dragNode) {
        const pt = this.toWorld(sx, sy);
        this.dragNode.x = pt.x;
        this.dragNode.y = pt.y;
      } else if (this.panning) {
        this.panX += sx - this.lastMouse.x;
        this.panY += sy - this.lastMouse.y;
      }
      this.lastMouse = { x: sx, y: sy };
    });

    window.addEventListener("mouseup", () => {
      this.dragNode = null;
      this.panning = false;
    });

    this.canvas.addEventListener("wheel", (e) => {
      e.preventDefault();
      const factor = e.deltaY < 0 ? 1.1 : 0.9;
      this.zoom = Math.max(0.35, Math.min(2.5, this.zoom * factor));
    }, { passive: false });
  }

          updateOverlay(n         )       {
    const box = $("cfgBlockOverlay");
    const deadTxt = n.is_dead ? `\n[NHÁNH CODE CHẾT UNSAT]: ${n.dead_reason || "Không thể đạt tới"}` : "";
    const lines = [
      `${n.label} (idom=B${n.idom}, số lệnh=${n.inst_count})${deadTxt}`,
      "----------------------------------------",
      ...n.instructions,
    ];
    box.textContent = lines.join("\n");
  }

          drawArrow(x1        , y1        , x2        , y2        , color        , dashed = false)       {
    const ctx = this.ctx;
    ctx.save();
    ctx.strokeStyle = color;
    ctx.fillStyle = color;
    ctx.lineWidth = 1.6;
    if (dashed) ctx.setLineDash([5, 4]);
    ctx.beginPath();
    ctx.moveTo(x1, y1);
    ctx.lineTo(x2, y2);
    ctx.stroke();

    const ang = Math.atan2(y2 - y1, x2 - x1);
    const len = 8;
    ctx.beginPath();
    ctx.moveTo(x2, y2);
    ctx.lineTo(x2 - len * Math.cos(ang - 0.38), y2 - len * Math.sin(ang - 0.38));
    ctx.lineTo(x2 - len * Math.cos(ang + 0.38), y2 - len * Math.sin(ang + 0.38));
    ctx.closePath();
    ctx.fill();
    ctx.restore();
  }

          animate = ()       => {
    this.drawFrame();
    if (this.graph && this.graph.nodes.length > 0) {
      this.animFrameId = requestAnimationFrame(this.animate);
    } else {
      this.animFrameId = null;
    }
  };

          drawFrame()       {
    const parent = this.canvas.parentElement;
    if (parent) {
      if (this.canvas.width !== parent.clientWidth || this.canvas.height !== parent.clientHeight) {
        this.canvas.width = Math.max(300, parent.clientWidth);
        this.canvas.height = Math.max(300, parent.clientHeight);
      }
    }
    const ctx = this.ctx;
    const pal = getCanvasPalette();
    ctx.clearRect(0, 0, this.canvas.width, this.canvas.height);

    if (this.graph && this.graph.nodes.length > 0) {
      const nodeMap = new Map                 ();
      for (const n of this.graph.nodes) nodeMap.set(n.id, n);

      ctx.save();
      ctx.translate(this.panX, this.panY);
      ctx.scale(this.zoom, this.zoom);

      if (this.showDom) {
        for (const de of this.graph.dom_edges) {
          const s = nodeMap.get(de.source);
          const t = nodeMap.get(de.target);
          if (s && t) {
            this.drawArrow((s.x ?? 0) - 10, s.y ?? 0, (t.x ?? 0) - 10, (t.y ?? 0) - 24, pal.cfgEdgeDom, true);
          }
        }
      }

      if (this.showDfg) {
        for (const fe of this.graph.dfg_edges) {
          const s = nodeMap.get(fe.source);
          const t = nodeMap.get(fe.target);
          if (s && t) {
            this.drawArrow((s.x ?? 0) + 12, s.y ?? 0, (t.x ?? 0) + 12, (t.y ?? 0) - 24, pal.cfgEdgeDfg, true);
          }
        }
      }

      for (const e of this.graph.edges) {
        const s = nodeMap.get(e.source);
        const t = nodeMap.get(e.target);
        if (!s || !t) continue;
        let col = pal.cfgEdgeDefault;
        let dashed = false;
        if (this.showDead && e.is_dead) {
          col = pal.cfgEdgeDead;
          dashed = true;
        } else if (e.kind === "true") col = pal.cfgEdgeTrue;
        else if (e.kind === "false") col = pal.cfgEdgeFalse;
        else if (e.kind === "back_edge") col = pal.cfgEdgeBack;
        this.drawArrow(s.x ?? 0, (s.y ?? 0) + 26, t.x ?? 0, (t.y ?? 0) - 26, col, dashed);
      }

      for (const n of this.graph.nodes) {
        const x = (n.x ?? 0) - 76;
        const y = (n.y ?? 0) - 26;
        let border = pal.cfgNodeBorder;
        let fill = pal.cfgNodeBg;
        if (this.showDead && n.is_dead) {
          border = pal.cfgNodeDeadBorder;
          fill = pal.cfgNodeDeadBg;
        } else if (n.is_entry) {
          border = pal.cfgNodeEntryBorder;
          fill = pal.cfgNodeEntryBg;
        } else if (n.has_sink) {
          border = pal.cfgNodeSinkBorder;
          fill = pal.cfgNodeSinkBg;
        } else if (n.is_loop_header) {
          border = pal.cfgNodeLoopBorder;
          fill = pal.cfgNodeLoopBg;
        } else if (n.is_exit) {
          border = pal.cfgNodeExitBorder;
          fill = pal.cfgNodeExitBg;
        }

        const isReplayFocus = this.activeReplayBlockId === n.id;
        if (isReplayFocus) {
          border = pal.cfgNodeReplayBorder;
          fill = pal.cfgNodeReplayBg;
        } else if (this.selectedId === n.id) {
          border = pal.cfgNodeSelectedBorder;
        }

        ctx.save();
        if (this.showDead && n.is_dead) {
          ctx.setLineDash([4, 3]);
        }
        ctx.fillStyle = fill;
        ctx.strokeStyle = border;
        ctx.lineWidth = isReplayFocus ? 3 : (this.selectedId === n.id ? 2.5 : 1.5);
        ctx.beginPath();
        ctx.roundRect(x, y, 152, 52, 6);
        ctx.fill();
        ctx.stroke();
        ctx.restore();

        ctx.fillStyle = pal.cfgText;
        ctx.font = "bold 11px Consolas, monospace";
        ctx.fillText(n.label.slice(0, 20), x + 8, y + 18);
        ctx.fillStyle = (this.showDead && n.is_dead) ? pal.cfgDeadSubText : pal.cfgSubText;
        ctx.font = "10px Consolas, monospace";
        const tag = (this.showDead && n.is_dead)
          ? "UNSAT CHẾT"
          : n.has_sink ? "ĐÍCH SINK" : n.is_loop_header ? "VÒNG LẶP" : n.is_entry ? "ĐẦU VÀO" : n.is_exit ? "KẾT THÚC" : "KHỐI";
        ctx.fillText(`${tag} | ${n.inst_count} lệnh`, x + 8, y + 38);
      }

      ctx.restore();
    }
  }
}

class HyperionStudio {
          cfgRenderer             ;
          jsWorkers           = [];
          jsStats = new Map                      ();
          catalog        = [];
          activeFnDetail      = null;
          traceSteps              = [];
          traceIndex = 0;
          sse                     = null;
          lastTelemetryHistory        = [];

  constructor() {
    this.cfgRenderer = new CfgRenderer($                   ("cfgCanvas"));
    this.bindUI();
    this.initTheme();
    this.drawTelemetryChart([]);
    this.loadSampleCode();
    this.loadEquivalenceSamples();
    this.refreshStatusOnce();
    this.refreshLeaderboard();
    setTimeout(() => this.connectSSE(), 3500);
  }

          initTheme()       {
    let saved                = null;
    try {
      saved = localStorage.getItem("hyperion-theme");
    } catch {
      saved = null;
    }
    const theme                   = saved === "light" ? "light" : "dark";
    this.applyTheme(theme);
  }

          applyTheme(theme                  )       {
    document.documentElement.dataset.theme = theme;
    try {
      localStorage.setItem("hyperion-theme", theme);
    } catch {
      // Bỏ qua nếu trình duyệt chặn localStorage
    }
    const btn = $("btnThemeToggle");
    if (btn) {
      const sun = btn.querySelector(".ico-sun");
      const moon = btn.querySelector(".ico-moon");
      if (sun) sun.classList.toggle("hidden", theme === "light");
      if (moon) moon.classList.toggle("hidden", theme === "dark");
    }
    const lbl = $("themeToggleLabel");
    if (lbl) {
      lbl.textContent = theme === "light" ? "Giao diện Tối" : "Giao diện Sáng";
    }
    this.cfgRenderer.redraw();
    this.drawTelemetryChart(this.lastTelemetryHistory);
  }

          toggleTheme()       {
    const current = document.documentElement.dataset.theme === "light" ? "light" : "dark";
    this.applyTheme(current === "light" ? "dark" : "light");
  }

          async refreshStatusOnce()                {
    try {
      const res = await fetch("/api/status");
      if (res.ok) {
        this.applySnapshot(await res.json());
      }
    } catch {
      // Bỏ qua lỗi mạng tạm thời
    }
  }

          bindUI()       {
    document.querySelectorAll(".tab").forEach((btn) => {
      btn.addEventListener("click", () => {
        const tab = (btn               ).dataset.tab ;
        document.querySelectorAll(".tab").forEach((b) => b.classList.remove("active"));
        document.querySelectorAll(".tab-view").forEach((v) => v.classList.remove("active"));
        btn.classList.add("active");
        $(`view-${tab}`).classList.add("active");
        if (tab === "cfg") {
          requestAnimationFrame(() => this.cfgRenderer.redraw());
        }
      });
    });

    document.querySelectorAll(".side-tab").forEach((btn) => {
      btn.addEventListener("click", () => {
        const paneId = (btn               ).dataset.sidePane ;
        document.querySelectorAll(".side-tab").forEach((b) => b.classList.remove("active"));
        document.querySelectorAll(".side-pane").forEach((p) => p.classList.remove("active"));
        btn.classList.add("active");
        $(paneId).classList.add("active");
      });
    });

    document.querySelectorAll(".sub-tab").forEach((btn) => {
      btn.addEventListener("click", () => {
        const subId = (btn               ).dataset.subTab ;
        document.querySelectorAll(".sub-tab").forEach((b) => b.classList.remove("active"));
        document.querySelectorAll(".sub-view").forEach((v) => v.classList.remove("active"));
        btn.classList.add("active");
        $(subId).classList.add("active");
      });
    });

    $("btnThemeToggle").addEventListener("click", () => this.toggleTheme());

    const syncRange = (inputId        , labelId        ) => {
      const inp = $                  (inputId);
      const lbl = $(labelId);
      inp.addEventListener("input", () => { lbl.textContent = inp.value; });
    };
    syncRange("cfgScale", "lblScale");
    syncRange("cfgWorkers", "lblWorkers");
    syncRange("cfgMaxRam", "lblMaxRam");
    syncRange("cfgRamArena", "lblRamArena");
    syncRange("cfgFreeFloor", "lblFreeFloor");
    syncRange("cfgTimeout", "lblTimeout");
    syncRange("cfgJsWorkers", "lblJsWorkers");

    $                   ("cfgCorpus").addEventListener("change", (e) => {
      const val = (e.target                     ).value;
      $("customPathWrap").classList.toggle("hidden", val !== "custom_path");
    });

    $("btnStart").addEventListener("click", () => this.startRun());
    $("btnEmergencyStop").addEventListener("click", () => this.emergencyStop());
    $("btnLoadSample").addEventListener("click", () => this.loadSampleCode());
    $("btnAnalyzeSnippet").addEventListener("click", () => this.analyzeSnippet());
    $("btnGenerateTests").addEventListener("click", () => this.generateUnitTests());
    $("btnCopyTests").addEventListener("click", () => this.copyGeneratedTests());
    $("btnProveEquiv").addEventListener("click", () => this.proveEquivalenceUI());
    $("btnKillMutants").addEventListener("click", () => this.killMutantsUI());
    $("btnRefreshBoard").addEventListener("click", () => this.refreshLeaderboard());
    $("btnResetGraph").addEventListener("click", () => this.cfgRenderer.resetLayout());
    $("fnSearch").addEventListener("input", () => this.renderFunctionCatalog());

    $("btnTracePrev").addEventListener("click", () => this.stepTrace(-1));
    $("btnTraceNext").addEventListener("click", () => this.stepTrace(1));
    $("btnTraceReset").addEventListener("click", () => this.setTraceStep(0));
    $("btnRunTraceReplay").addEventListener("click", () => this.runTraceReplayUI());

    $                   ("testFrameworkSelect").addEventListener("change", () => this.renderGeneratedTestsView());
    $                  ("chkShowDead").addEventListener("change", (e) => {
      this.cfgRenderer.showDead = (e.target                    ).checked;
      this.cfgRenderer.redraw();
    });
    $                  ("chkShowDom").addEventListener("change", (e) => {
      this.cfgRenderer.showDom = (e.target                    ).checked;
      this.cfgRenderer.redraw();
    });
    $                  ("chkShowDfg").addEventListener("change", (e) => {
      this.cfgRenderer.showDfg = (e.target                    ).checked;
      this.cfgRenderer.redraw();
    });
  }

          loadSampleCode()       {
    const lang = $                   ("pgLang").value;
    $                     ("srcEditor").value = lang === "python" ? SAMPLE_PY : SAMPLE_TS;
  }

          loadEquivalenceSamples()       {
    $                     ("equivOldEditor").value = SAMPLE_EQUIV_OLD_PY;
    $                     ("equivNewEditor").value = SAMPLE_EQUIV_NEW_PY;
  }

          connectSSE()       {
    if (this.sse) this.sse.close();
    this.sse = new EventSource("/api/stream");
    this.sse.onmessage = (ev) => {
      try {
        const data = JSON.parse(ev.data);
        this.applySnapshot(data);
      } catch {
        // Bỏ qua khung SSE lỗi tạm thời
      }
    };
  }

          startWebWorkers(count        )       {
    this.stopWebWorkers();
    for (let i = 0; i < count; i++) {
      const w = new Worker("/dist/compute_worker.js");
      w.onmessage = (ev) => {
        const d = ev.data;
        if (d?.type === "stats") {
          const prev = this.jsStats.get(d.workerId)?.satSolved ?? 0;
          this.jsStats.set(d.workerId, {
            id: d.workerId,
            satSolved: prev + d.satSolved,
            clausesPerSec: d.clausesPerSec,
          });
          $("gWebWorkers").textContent = String(this.jsWorkers.length);
        }
      };
      w.postMessage({ type: "start", workerId: i, seed: 424242 });
      this.jsWorkers.push(w);
    }
    $("gWebWorkers").textContent = String(this.jsWorkers.length);
  }

          stopWebWorkers()       {
    for (const w of this.jsWorkers) {
      w.postMessage({ type: "stop" });
      w.terminate();
    }
    this.jsWorkers = [];
    this.jsStats.clear();
    $("gWebWorkers").textContent = "0";
  }

          async startRun()                {
    const payload = {
      mode: $                   ("cfgMode").value,
      corpus_source: $                   ("cfgCorpus").value,
      custom_path: $                  ("cfgCustomPath").value,
      intensity: $                   ("cfgIntensity").value,
      scale_factor: Number($                  ("cfgScale").value),
      enable_optimizer: $                  ("chkOpt").checked,
      enable_abstract_interp: $                  ("chkAi").checked,
      enable_symbolic: $                  ("chkSym").checked,
      enable_mutation: $                  ("chkMut").checked,
      safety: {
        max_workers: Number($                  ("cfgWorkers").value),
        max_process_ram_mb: Number($                  ("cfgMaxRam").value),
        ram_arena_mb: Number($                  ("cfgRamArena").value),
        min_free_system_ram_pct: Number($                  ("cfgFreeFloor").value),
        max_duration_sec: Number($                  ("cfgTimeout").value),
        below_normal_priority: true,
      },
    };

    const res = await fetch("/api/run", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(payload),
    });
    const out = await res.json();
    if (out.ok && $                  ("chkWebWorkerStress").checked) {
      this.startWebWorkers(Number($                  ("cfgJsWorkers").value));
    }
  }

          async emergencyStop()                {
    this.stopWebWorkers();
    await fetch("/api/stop", { method: "POST" });
  }

          async analyzeSnippet()                {
    const code = $                     ("srcEditor").value;
    const language = $                   ("pgLang").value;
    const kill_mutants = $                  ("chkAnalyzeKillMutants").checked;
    const res = await fetch("/api/analyze-snippet", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ code, language, kill_mutants }),
    });
    const data = await res.json();
    if (data.functions && data.functions.length > 0) {
      this.inspectFunctionObject(data.functions[0]);
    } else if (data.parse_errors?.length) {
      $("ssaViewer").textContent = "Lỗi phân tích cú pháp:\n" + data.parse_errors.join("\n");
    } else if (data.error) {
      $("ssaViewer").textContent = `Lỗi: ${data.error}`;
    }
  }

          async generateUnitTests()                {
    const code = $                     ("srcEditor").value;
    const language = $                   ("pgLang").value;
    const framework = $                   ("testFrameworkSelect").value;
    const include_mutant_killers = $                  ("chkAnalyzeKillMutants").checked;

    const res = await fetch("/api/generate-tests", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ code, language, framework, include_mutant_killers }),
    });
    const data = await res.json();
    if (data.functions && data.functions.length > 0) {
      if (!this.activeFnDetail) this.activeFnDetail = {};
      this.activeFnDetail.generated_tests = data.functions[0];
      this.renderGeneratedTestsView();
    } else if (data.error) {
      $("testGenViewer").textContent = `Lỗi sinh unit test: ${data.error}`;
    }
  }

          renderGeneratedTestsView()       {
    const fw = $                   ("testFrameworkSelect").value;
    const gt = this.activeFnDetail?.generated_tests;
    if (!gt) return;
    $("testGenViewer").textContent = gt[fw] || gt.pytest || "// Chưa có dữ liệu unit test.";
  }

          async copyGeneratedTests()                {
    const txt = $("testGenViewer").textContent || "";
    try {
      await navigator.clipboard.writeText(txt);
    } catch {
      // Bỏ qua nếu môi trường không hỗ trợ clipboard
    }
  }

          async proveEquivalenceUI()                {
    const old_code = $                     ("equivOldEditor").value;
    const new_code = $                     ("equivNewEditor").value;
    const language = $                   ("pgLang").value;
    const box = $("equivResultBox");
    box.textContent = "Đang chạy bộ giải DPLL(T) để kiểm chứng tương đương...";

    const res = await fetch("/api/equivalence", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ old_code, new_code, language }),
    });
    const data = await res.json();
    const lines = [
      `Trạng thái: ${data.status || "ERROR"} (${data.equivalent ? "TƯƠNG ĐƯƠNG" : "KHÔNG TƯƠNG ĐƯƠNG"})`,
      `Kết luận  : ${data.summary || data.error || ""}`,
      `Chi tiết  : ${data.paths_checked ?? 0} cặp đường chạy | ${data.smt_queries ?? 0} truy vấn DPLL(T)`,
    ];
    if (data.counterexample) {
      lines.push(`Phản ví dụ đầu vào: ${JSON.stringify(data.counterexample.inputs)}`);
      lines.push(`Đầu ra Hàm Cũ: ${JSON.stringify(data.counterexample.old_output)}`);
      lines.push(`Đầu ra Hàm Mới: ${JSON.stringify(data.counterexample.new_output)}`);
    }
    box.textContent = lines.join("\n");
  }

          async killMutantsUI()                {
    const code = $                     ("srcEditor").value;
    const language = $                   ("pgLang").value;
    const summaryBox = $("mutantKillSummary");
    summaryBox.textContent = "Đang dùng DPLL(T) tìm nhân chứng tiêu diệt các đột biến SURVIVED...";

    const res = await fetch("/api/kill-mutants", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ code, language }),
    });
    const data = await res.json();
    if (data.error && !data.mutation) {
      summaryBox.textContent = `Lỗi: ${data.error}`;
      return;
    }

    const lines = [
      `Hàm: ${data.function} | Sống sót ban đầu: ${data.initial_survived} | Đã diệt thêm bằng SMT: ${data.newly_killed} | Còn sống: ${data.remaining_survived} | Điểm mới: ${data.new_score_pct}%`,
    ];
    for (const w of data.kill_witnesses || []) {
      lines.push(`- Đột biến #${w.mutant_id} (${w.operator} dòng ${w.line}): đầu vào ${JSON.stringify(w.witness_inputs)} | Gốc=${JSON.stringify(w.orig_output)} vs Đột biến=${JSON.stringify(w.mut_output)}`);
    }
    summaryBox.textContent = lines.join("\n");

    if (this.activeFnDetail) {
      this.activeFnDetail.mutation = data.mutation;
      if (data.appended_tests) {
        this.activeFnDetail.generated_tests = data.appended_tests;
        this.renderGeneratedTestsView();
      }
      this.renderMutationTable(data.mutation?.records || []);
    }
  }

          async runTraceReplayUI()                {
    const rawInputs = $                  ("traceInputsInput").value.trim() || "{}";
    let inputs                         ;
    try {
      inputs = JSON.parse(rawInputs);
    } catch {
      $("traceStepDetailBox").textContent = "Lỗi: Chuỗi JSON tham số đầu vào không hợp lệ.";
      return;
    }

    const code = $                     ("srcEditor").value;
    const language = $                   ("pgLang").value;
    const res = await fetch("/api/trace-replay", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ code, language, inputs }),
    });
    const data = await res.json();
    if (data.trace_steps) {
      this.loadTraceSteps(data.trace_steps);
    } else if (data.error) {
      $("traceStepDetailBox").textContent = `Lỗi tua vết: ${data.error}`;
    }
  }

          loadTraceSteps(steps             )       {
    this.traceSteps = steps || [];
    this.setTraceStep(0);
  }

          stepTrace(delta        )       {
    if (!this.traceSteps.length) return;
    const next = Math.max(0, Math.min(this.traceSteps.length - 1, this.traceIndex + delta));
    this.setTraceStep(next);
  }

          setTraceStep(idx        )       {
    if (!this.traceSteps.length) {
      this.traceIndex = 0;
      $("traceStepLabel").textContent = "Bước 0/0";
      $("traceStepDetailBox").textContent = "Chưa có dữ liệu tua vết thực thi.";
      this.cfgRenderer.setActiveReplayBlock(null);
      return;
    }
    this.traceIndex = Math.max(0, Math.min(this.traceSteps.length - 1, idx));
    const st = this.traceSteps[this.traceIndex];
    $("traceStepLabel").textContent = `Bước ${this.traceIndex + 1}/${this.traceSteps.length} (B${st.block_id})`;
    this.cfgRenderer.setActiveReplayBlock(st.block_id);
    $("traceStepDetailBox").textContent = [
      `Bước #${st.step} | Khối B${st.block_id} (${st.block_label}) | Dòng ${st.line} | Sự kiện: ${st.event}`,
      `Lệnh SSA  : ${st.instruction}`,
      `Giá trị biến: ${JSON.stringify(st.vars)}`,
      `Khoảng giá trị: ${JSON.stringify(st.intervals)}`,
    ].join("\n");
  }

          async selectFunction(fnId        )                {
    const res = await fetch(`/api/function/${fnId}`);
    if (!res.ok) return;
    const detail = await res.json();
    this.inspectFunctionObject(detail);
  }

          inspectFunctionObject(fn     )       {
    this.activeFnDetail = fn;
    $("cfgFnName").textContent = `${fn.name} (${fn.language})`;
    $("cfgFnMeta").textContent = `Khối: ${fn.blocks} | Độ phức tạp: ${fn.cyclomatic_complexity} | Vòng lặp: ${fn.loop_count} | Diệt đột biến: ${fn.mutation?.score_pct ?? 0}%`;

    this.cfgRenderer.setGraph(fn.cfg_graph || null);
    $                     ("srcEditor").value = fn.source_code || "";
    $("ssaViewer").textContent = fn.ssa_dump || "";

    const ivLines = Object.entries(fn.intervals || {}).map(([k, v]) => `${k.padEnd(20)} : ${v}`);
    const taintLine = fn.tainted_vars?.length ? `\nBiến SSA nhiễm bẩn: ${fn.tainted_vars.join(", ")}` : "\nBiến SSA nhiễm bẩn: không có";
    const aiLines = (fn.ai_findings || []).map((f     ) => `[${f.severity}] Dòng ${f.line}: ${f.kind} — ${f.message}`);
    $("aiIntervalsBox").textContent = [...ivLines, taintLine, "", ...aiLines].join("\n") || "Không có dữ liệu khoảng giá trị.";

    const cxLines = (fn.counterexamples || []).map(
      (c     ) => `[${c.severity}] ${c.kind} @ Dòng ${c.line} (B${c.block_id})\n  ${c.description}\n  Đầu vào: ${JSON.stringify(c.inputs)}\n  Đường chạy: ${c.path_blocks.map((b        ) => "B" + b).join(" -> ")}`
    );
    $("cxDetailBox").textContent = cxLines.join("\n\n") || "Không phát hiện phản ví dụ lỗi trên các đường chạy đã duyệt.";

    const deadLines = (fn.dead_branches || []).map(
      (d     ) => `[UNSAT] Khối B${d.block_id} -> B${d.target_block_id} (Dòng ${d.line}): ${d.reason}`
    );
    $("deadBranchesBox").textContent = deadLines.join("\n") || "Không phát hiện nhánh code chết UNSAT nào.";

    const firstCxWithTrace = (fn.counterexamples || []).find((c     ) => Array.isArray(c.trace_steps) && c.trace_steps.length > 0);
    if (firstCxWithTrace) {
      $                  ("traceInputsInput").value = JSON.stringify(firstCxWithTrace.inputs || {});
      this.loadTraceSteps(firstCxWithTrace.trace_steps);
    } else {
      this.loadTraceSteps([]);
    }

    if (fn.generated_tests) {
      this.renderGeneratedTestsView();
    }
    this.renderMutationTable(fn.mutation?.records || []);
  }

          renderMutationTable(records       )       {
    const statusMap                         = {
      KILLED: "KILLED",
      SURVIVED: "SURVIVED",
      TIMEOUT: "TIMEOUT",
    };
    const tbody = $                         ("mutationTable").querySelector("tbody") ;
    tbody.innerHTML = "";
    for (const r of records) {
      const stLabel = statusMap[r.status] || r.status;
      const tr = document.createElement("tr");
      tr.innerHTML = `
        <td>#${r.mutant_id}</td>
        <td><code>${r.operator}</code></td>
        <td>B${r.block_id} / D${r.line}</td>
        <td><code>${this.escapeHtml(r.original)}</code></td>
        <td><code>${this.escapeHtml(r.mutated)}</code></td>
        <td class="st-${r.status}">${stLabel}${r.killed_by_smt ? " (SMT)" : ""}</td>
        <td>${r.steps_executed}</td>
      `;
      tbody.appendChild(tr);
    }
  }

          applySnapshot(snap     )       {
    const m = snap.machine || {};
    $("machineBanner").textContent = `${m.cpu_model || "CPU"} | ${m.logical_cores || "?"} luồng xử lý | ${m.total_ram_gb || "?"} GB RAM | ${m.hostname || ""}`;

    const hw = snap.hardware || {};
    $("gCpu").textContent = `${Number(hw.cpu_load_pct || 0).toFixed(1)}%`;
    $("gFreeRam").textContent = `${Number(hw.free_ram_pct || 0).toFixed(1)}% (${Math.round(hw.avail_ram_mb || 0)} MB)`;
    $("gProcRam").textContent = `${Math.round(hw.process_ram_mb || 0)} MB`;

    const badge = $("stateBadge");
    const st = String(snap.state || "IDLE");
    badge.textContent = st;
    badge.className = `status-pill state-${st.toLowerCase()}`;

    if (st !== "RUNNING" && this.jsWorkers.length > 0) {
      this.stopWebWorkers();
      this.refreshLeaderboard();
    }
    if (st === "COMPLETED" && snap.last_run_id) {
      this.refreshLeaderboard();
    }

    const banner = $("safetyBanner");
    if (snap.stop_reason && (st === "SAFETY_TRIPPED" || st === "STOPPED")) {
      banner.textContent = `CẦU CHÌ BẢO VỆ / ĐÃ DỪNG: ${snap.stop_reason}`;
      banner.classList.remove("hidden");
    } else {
      banner.classList.add("hidden");
    }

    const sc = snap.scores || {};
    const tot = snap.totals || {};
    $("scComposite").textContent = String(sc.composite_score ?? 0);
    $("scSsa").textContent = String(sc.ssa_cfg_score ?? 0);
    $("scSmt").textContent = String(sc.smt_symbolic_score ?? 0);
    $("scMut").textContent = String(sc.mutation_score ?? 0);
    $("totInsts").textContent = String(tot.ssa_instructions ?? 0);
    $("totSmt").textContent = String(tot.smt_queries ?? 0);
    $("totMut").textContent = String(tot.mutants_evaluated ?? 0);
    $("totVmSteps").textContent = String(tot.vm_steps ?? 0);
    $("totCx").textContent = String(tot.counterexamples ?? 0);
    $("totAi").textContent = String(tot.ai_findings ?? 0);

    const pct = snap.progress?.pct ?? 0;
    $("progressFill").style.width = `${pct}%`;
    $("runProgressText").textContent = `${snap.progress?.completed_units ?? 0}/${snap.progress?.total_units ?? 0} đơn vị (${snap.duration_sec ?? 0} giây)`;

    this.lastTelemetryHistory = snap.telemetry_history || [];
    this.drawTelemetryChart(this.lastTelemetryHistory);
    this.renderWorkers(snap.workers || []);
    this.renderFindings(snap.findings || []);

    if (Array.isArray(snap.functions) && snap.functions.length !== this.catalog.length) {
      this.catalog = snap.functions;
      this.renderFunctionCatalog();
      if (!this.activeFnDetail && this.catalog.length > 0) {
        this.selectFunction(this.catalog[0].id);
      }
    }
  }

          renderWorkers(pyWorkers       )       {
    const grid = $("workerGrid");
    const cards           = [];
    for (const w of pyWorkers) {
      cards.push(`
        <div class="worker-card">
          <div><strong>PY PID ${w.pid}</strong></div>
          <div>Đơn vị: ${w.units} | Hàm: ${w.functions}</div>
          <div>SMT: ${w.smt_queries} | Đột biến: ${w.mutants}</div>
          <div>Thời gian: ${w.busy_sec} giây</div>
        </div>
      `);
    }
    this.jsStats.forEach((jw) => {
      cards.push(`
        <div class="worker-card js-worker">
          <div><strong>LUỒNG JS #${jw.id}</strong></div>
          <div>3-SAT đã giải: ${jw.satSolved}</div>
          <div>Tốc độ: ${jw.clausesPerSec} mệnh đề/s</div>
        </div>
      `);
    });
    grid.innerHTML = cards.join("") || '<div class="empty-msg">Các luồng đang rảnh. Khi chạy sẽ tự khóa ở mức ưu tiên thấp.</div>';
  }

          renderFindings(findings       )       {
    const box = $("findingsFeed");
    if (!findings.length) {
      box.innerHTML = '<div class="empty-msg">Chưa ghi nhận phát hiện lỗi nào.</div>';
      return;
    }
    const sevLabels                         = {
      CRITICAL: "CRITICAL",
      HIGH: "HIGH",
      MEDIUM: "MEDIUM",
      LOW: "LOW",
    };
    box.innerHTML = findings.slice(0, 30).map((f) => {
      const sev = sevLabels[f.severity] || f.severity || "INFO";
      return `
      <div class="finding-row sev-${this.escapeHtml(sev)}">
        <span class="sev-tag">${this.escapeHtml(sev)}</span>
        <div>
          <strong>${this.escapeHtml(f.kind)}</strong> trong <code>${this.escapeHtml(f.function)}</code> (Dòng ${f.line}) —
          ${this.escapeHtml(f.message)}
        </div>
      </div>
    `;
    }).join("");
  }

          renderFunctionCatalog()       {
    const q = $                  ("fnSearch").value.toLowerCase();
    const list = $("fnList");
    const filtered = this.catalog.filter((f) => f.name.toLowerCase().includes(q));
    $("fnCount").textContent = String(this.catalog.length);
    if (!filtered.length) {
      list.innerHTML = '<div class="empty-msg">Không tìm thấy hàm nào phù hợp.</div>';
      return;
    }
    list.innerHTML = "";
    for (const f of filtered.slice(0, 80)) {
      const div = document.createElement("div");
      div.className = `fn-item ${this.activeFnDetail?.id === f.id ? "active" : ""}`;
      div.innerHTML = `
        <div class="fn-name">${this.escapeHtml(f.name)}</div>
        <div class="fn-meta">${f.language} | Khối:${f.blocks} CC:${f.cyclomatic_complexity} | Lỗi:${f.counterexamples} | Diệt:${f.mutation_score_pct}%</div>
      `;
      div.addEventListener("click", () => this.selectFunction(f.id));
      list.appendChild(div);
    }
  }

          drawTelemetryChart(hist       )       {
    const canvas = $                   ("telemetryCanvas");
    const ctx = canvas.getContext("2d") ;
    const pal = getCanvasPalette();
    const w = canvas.width;
    const h = canvas.height;
    ctx.clearRect(0, 0, w, h);

    ctx.strokeStyle = pal.grid;
    ctx.lineWidth = 1;
    for (let i = 1; i < 4; i++) {
      const y = (h / 4) * i;
      ctx.beginPath();
      ctx.moveTo(0, y);
      ctx.lineTo(w, y);
      ctx.stroke();
    }
    for (let i = 1; i < 6; i++) {
      const x = (w / 6) * i;
      ctx.beginPath();
      ctx.moveTo(x, 0);
      ctx.lineTo(x, h);
      ctx.stroke();
    }

    ctx.fillStyle = pal.axisLabel;
    ctx.font = "10px Consolas, monospace";
    ctx.fillText("100%", 6, 14);
    ctx.fillText("50%", 6, h / 2 - 4);
    ctx.fillText("0%", 6, h - 6);

    if (hist.length < 2) return;

    const plotLine = (vals          , maxVal        , color        ) => {
      ctx.strokeStyle = color;
      ctx.lineWidth = 2;
      ctx.beginPath();
      vals.forEach((v, idx) => {
        const x = (idx / (vals.length - 1)) * (w - 16) + 8;
        const norm = Math.min(1, Math.max(0, v / maxVal));
        const y = h - 10 - norm * (h - 20);
        if (idx === 0) ctx.moveTo(x, y);
        else ctx.lineTo(x, y);
      });
      ctx.stroke();
    };

    const maxRate = Math.max(100, ...hist.map((p) => Math.max(p.smt_per_sec || 0, p.mutants_per_sec || 0)));
    plotLine(hist.map((p) => p.cpu_pct || 0), 100, pal.cpu);
    plotLine(hist.map((p) => p.free_ram_pct || 0), 100, pal.ram);
    plotLine(hist.map((p) => p.smt_per_sec || 0), maxRate, pal.smt);
    plotLine(hist.map((p) => p.mutants_per_sec || 0), maxRate, pal.mut);
  }

          async refreshLeaderboard()                {
    const res = await fetch("/api/leaderboard");
    if (!res.ok) return;
    const data = await res.json();
    const tbody = $                         ("leaderboardTable").querySelector("tbody") ;
    tbody.innerHTML = "";
    (data.runs || []).forEach((r     , idx        ) => {
      const tr = document.createElement("tr");
      tr.innerHTML = `
        <td>#${idx + 1}</td>
        <td><strong>${this.escapeHtml(r.hostname)}</strong><br/><small>${this.escapeHtml(r.cpu_model)}</small></td>
        <td>${r.logical_cores} luồng / ${r.total_ram_gb}GB</td>
        <td>${this.escapeHtml(r.mode)} (${this.escapeHtml(r.corpus_source)})</td>
        <td><strong>${r.composite_score}</strong></td>
        <td>${r.ssa_cfg_score}</td>
        <td>${r.smt_symbolic_score}</td>
        <td>${r.mutation_score}</td>
        <td>${r.duration_sec} giây</td>
      `;
      tbody.appendChild(tr);
    });
  }

          escapeHtml(s        )         {
    return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
  }
}

window.addEventListener("DOMContentLoaded", () => {
  new HyperionStudio();
});
