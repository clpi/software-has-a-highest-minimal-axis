function mulberry(seed){ var a=seed>>>0; return function(){ a|=0; a=a+0x6D2B79F5|0; var t=Math.imul(a^a>>>15,1|a); t=t+Math.imul(t^t>>>7,61|t)^t; return ((t^t>>>14)>>>0)/4294967296; }; }

function cloneState(s){ return JSON.parse(JSON.stringify(s)); }
function vecDominates(a,b){ return a[0]<=b[0] && a[1]<=b[1] && (a[0]<b[0]||a[1]<b[1]); }
function vecFrontier(cands){ return cands.filter(function(c){ return !cands.some(function(o){ return o!==c && vecDominates(o.vec,c.vec); }); }); }
function planEntropy(steps){
  if(!steps || steps.length<=1) return 0;
  var counts={}, n=steps.length;
  steps.forEach(function(s){ counts[s.label]=(counts[s.label]||0)+1; });
  var h=0;
  Object.keys(counts).forEach(function(k){ var p=counts[k]/n; h-=p*Math.log2(p); });
  return h;
}

var MATS={
  stone:{mu:0.85, slide:0, col:"#8d8578"},
  wood:{mu:0.60, slide:1, col:"#b07d4f"},
  mud:{mu:0.40, slide:2, col:"#7a5c3e"},
  rubber:{mu:0.98, slide:0, col:"#3c4148"},
  ice:{mu:0.08, slide:4, col:"#a9d6ea"}
};
var MATNAMES=["stone","wood","mud","rubber","ice"];

var PK={level:2, count:4, place:"scatter", matMode:"global", mat:"stone", motion:"off", period:8};

function planScore(c, W){ return W.steps*c.vec[0] + W.specials*c.vec[1] + W.slides*(c.vec[3]||0) - W.entropy*(c.vec[2]||0); }
function selectPlanW(cands, W){
  if(!cands || !cands.length) return null;
  var fr=vecFrontier(cands).slice().sort(function(a,b){ return planScore(a,W)-planScore(b,W) || a.vec[0]-b.vec[0] || a.vec[1]-b.vec[1] || ((b.vec[2]||0)-(a.vec[2]||0)); });
  return fr[0];
}

function mkSteps(start, edges, posOf){
  var steps=[], cur=start;
  edges.forEach(function(e){
    var before=cloneState(cur), after=cloneState(e.to);
    steps.push({label:e.label, inv:e.inv, kind:e.kind||"move", arc:!!e.arc, special:e.special?1:0, slide:e.slide||0, before:before, after:after, fromPos:posOf(before), toPos:posOf(after)});
    cur=e.to;
  });
  return steps;
}
function candFromEdges(name, start, edges, posOf){
  var steps=mkSteps(start, edges, posOf);
  var sp=0, sl=0; steps.forEach(function(s){ sp+=s.special; sl+=s.slide||0; });
  var ent=planEntropy(steps);
  return {name:name, steps:steps, vec:[steps.length, sp, ent, sl], entropy:ent, slides:sl, hits:1};
}
function dijkstraPlan(start, keyFn, expandFn, goalFn, ws, wj){
  var open=[{s:start, cost:0, path:[]}], seen={};
  seen[keyFn(start)]=0;
  var guard=0;
  while(open.length && guard++<20000){
    open.sort(function(a,b){ return a.cost-b.cost; });
    var cur=open.shift();
    if(goalFn(cur.s)) return cur.path;
    if(seen[keyFn(cur.s)]<cur.cost) continue;
    expandFn(cur.s).forEach(function(e){
      var c=cur.cost + ws + wj*(e.special?1:0), nk=keyFn(e.to);
      if(seen[nk]==null || c<seen[nk]){ seen[nk]=c; open.push({s:e.to, cost:c, path:cur.path.concat([e])}); }
    });
  }
  return null;
}
function stdPlans(name, start, keyFn, expandFn, goalFn, posOf){
  var profiles=[["fewest steps",1,0.05],["fewest special actions",0.4,1],["balanced",1,1]], seen={}, out=[];
  profiles.forEach(function(p){
    var edges=dijkstraPlan(start, keyFn, expandFn, goalFn, p[1], p[2]);
    if(!edges) return;
    var key=edges.map(function(e){ return e.label; }).join(",");
    if(seen[key]){ out.forEach(function(c){ if(c._key===key) c.hits++; }); return; }
    seen[key]=1;
    var c=candFromEdges(name+" · "+p[0], start, edges, posOf); c._key=key; out.push(c);
  });
  return out;
}

function platOff(b, t, period){ if(!b.mov) return {dx:0, dy:0}; var s=Math.sin(2*Math.PI*t/period); return b.axis==="h" ? {dx:Math.round(b.amp*s), dy:0} : {dx:0, dy:Math.round(b.amp*s)}; }

function platCells(st){
  var b=st.blocks, c=b._c;
  if(c && c.tick===st.tick && c.period===st.period) return c.map;
  var map={};
  b.forEach(function(bl){ var o=platOff(bl, st.tick, st.period); for(var i=0;i<bl.w;i++) for(var j=0;j<bl.h;j++) map[(bl.x+o.dx+i)+","+(bl.y+o.dy+j)]=bl.mat; });
  b._c={tick:st.tick, period:st.period, map:map};
  return map;
}
function platSolidAt(st,x,y){ return y>=11 || !!platCells(st)[x+","+y]; }
function platLandAt(st,x,y){ while(y<10 && !platSolidAt(st,x,y+1)) y++; return y; }
function platStand(st,x,y){ while(y>0 && platSolidAt(st,x,y)) y--; return platLandAt(st,x,y); }
function platSurfaceMat(st,x,y){ if(y+1>=11) return st.groundMat; return platCells(st)[x+","+(y+1)] || st.groundMat; }
function platSlide(st, dir){
  if(!dir) return 0;
  var budget=(MATS[platSurfaceMat(st, st.ax, st.ay)]||MATS.stone).slide, n=0;
  while(n<budget){
    var nx=st.ax+dir;
    if(nx<0||nx>23) break;
    if(platSolidAt(st,nx,st.ay)) break;
    if(!platSolidAt(st,nx,st.ay+1)) break;
    st.ax=nx; n++;
  }
  return n;
}
function platExpand(st){
  var out=[], ax=st.ax, ay=st.ay, t1=st.tick+1;
  function base(nx){ return {ax:nx, ay:ay, gx:st.gx, tick:t1, groundMat:st.groundMat, period:st.period, blocks:st.blocks}; }
  function land(nx, fromY, dir){
    var s1=base(nx); s1.ay=platStand(s1, nx, fromY);
    var sl=platSlide(s1, dir);
    return {st:s1, slide:sl};
  }
  function sfx(n){ return n>0 ? "+SLIDE"+n : ""; }
  [[-1,"MOVE_L","MOVE_R"],[1,"MOVE_R","MOVE_L"]].forEach(function(d){
    var nx=ax+d[0]; if(nx<0||nx>23) return;
    if(platSolidAt(base(nx),nx,ay)) return;
    var r=land(nx, ay, d[0]);
    out.push({label:d[1]+sfx(r.slide), inv:d[2], kind:"move", special:0, slide:r.slide, to:r.st});
  });
  [[-1,"JUMP_L","JUMP_R"],[1,"JUMP_R","JUMP_L"]].forEach(function(d){
    var nx=ax+d[0]; if(nx<0||nx>23) return;
    var probe=base(nx);
    if(platSolidAt(probe,ax,ay-1)||platSolidAt(probe,ax,ay-2)||platSolidAt(probe,nx,ay-2)) return;
    var r=land(nx, ay-2, d[0]);
    out.push({label:d[1]+sfx(r.slide), inv:d[2], kind:"jump", arc:true, special:1, slide:r.slide, to:r.st});
  });
  [[-2,"JUMP_OVER_L","JUMP_OVER_R"],[2,"JUMP_OVER_R","JUMP_OVER_L"]].forEach(function(d){
    var nx=ax+d[0]; if(nx<0||nx>23) return; var mid=ax+d[0]/2;
    var probe=base(nx);
    if(platSolidAt(probe,ax,ay-1)||platSolidAt(probe,ax,ay-2)||platSolidAt(probe,mid,ay-2)||platSolidAt(probe,nx,ay-2)) return;
    var r=land(nx, ay-2, d[0]);
    out.push({label:d[1]+sfx(r.slide), inv:d[2], kind:"jump", arc:true, special:1, slide:r.slide, to:r.st});
  });
  if(st.blocks.some(function(b){ return b.mov; })){
    var rw=land(ax, ay, 0);
    out.push({label:"WAIT", inv:"WAIT", kind:"wait", special:0, slide:0, to:rw.st});
  }
  return out;
}

var SCEN={
  platform:{
    posOf:function(st){ return {x:st.ax*30+15, y:st.ay*30+15}; },
    make:function(rng, K){
      K=K||PK;
      var blocks=[], cols=[], guard=0;
      while(cols.length<K.count && guard++<300){ var c=3+Math.floor(rng()*17); if(cols.indexOf(c)<0) cols.push(c); }
      cols.forEach(function(c){
        var mat = K.matMode==="mixed" ? MATNAMES[Math.floor(rng()*MATNAMES.length)] : K.mat;
        if(K.place==="scatter"){ var hs=rng()<0.45?2:1; blocks.push({x:c, y:11-hs, w:1, h:hs, mat:mat, mov:0, axis:"h", amp:2}); }
        else if(K.place==="columns"){ var hc=2+Math.floor(rng()*2); blocks.push({x:c, y:11-hc, w:1, h:hc, mat:mat, mov:0, axis:"h", amp:2}); }
        else if(K.place==="floating"){ blocks.push({x:c, y:5+Math.floor(rng()*4), w:rng()<0.4?2:1, h:1, mat:mat, mov:0, axis:"h", amp:2}); }
        else { blocks.push({x:c, y:rng()<0.5?10:8, w:2+Math.floor(rng()*3), h:1, mat:mat, mov:0, axis:"h", amp:2}); }
      });
      if(K.motion!=="off"){
        var anyMover=false;
        blocks.forEach(function(b,i){
          if(K.motion==="v" && b.y>=10) return;
          if(i%2===0 || blocks.length<=2){ b.mov=1; b.axis=K.motion; b.amp=K.motion==="h"?2:1; anyMover=true; }
        });
        if(K.motion==="v" && !anyMover && blocks.length){ blocks[0].y=9; blocks[0].h=1; blocks[0].mov=1; blocks[0].axis="v"; blocks[0].amp=1; }
      }
      var st={ax:1, ay:10, gx:21, tick:0, groundMat:K.mat, period:K.period, blocks:blocks};
      st.ay=platStand(st,1,10);
      return st;
    },
    buildPlans:function(st){
      var phased=st.blocks.some(function(b){ return b.mov; });
      var keyFn= phased ? function(s){ return s.ax+","+s.ay+","+(s.tick%s.period); } : function(s){ return s.ax+","+s.ay; };
      return stdPlans("platform route", st, keyFn, platExpand, function(s){ return s.ax>=s.gx; }, SCEN.platform.posOf);
    },
    goal:function(st){ return st.ax>=st.gx; },

  }
};

var HMA_AXES=[
  {name:"count", values:[0,4]},
  {name:"place", values:["scatter","columns","floating","wide"]},
  {name:"material", values:["stone","ice","mixed"]},
  {name:"motion", values:["off","h","v"]},
  {name:"wsteps", values:[0.4,1]},
  {name:"wspecials", values:[0.05,1]},
  {name:"wentropy", values:[0,0.5]},
  {name:"wslides", values:[0,1]}
];
var HMA_COMPS=["layout","successors","plan","selection","execution"];
var HMA_EDGES=[
  {components:["layout","successors","plan"], weight:1},
  {components:["successors","plan","execution"], weight:1},
  {components:["plan","selection","execution"], weight:1},
  {components:["successors","execution"], weight:1}
];
var HMA={sig:null, instance:null, result:null, physCache:{}, timer:null};

function hmaContract(){
  var rows=[[]];
  HMA_AXES.forEach(function(ax){
    var next=[];
    rows.forEach(function(r){ ax.values.forEach(function(v){ next.push(r.concat([v])); }); });
    rows=next;
  });
  return rows;
}
function hmaKeyFn(st){
  var phased=st.blocks.some(function(b){ return b.mov; });
  return phased ? function(s){ return s.ax+","+s.ay+","+(s.tick%s.period); }
                : function(s){ return s.ax+","+s.ay; };
}
/* One physical episode: layout, successors, plan for one (count, place, material,
   motion) at the current seed and period. Weight-only changes reuse it. */
function hmaEpisode(count, place, material, motion, seed, period){
  var key=seed+"|"+period+"|"+count+"|"+place+"|"+material+"|"+motion;
  if(HMA.physCache[key]) return HMA.physCache[key];
  var K = material==="mixed"
    ? {level:0, count:count, place:place, matMode:"mixed", mat:"stone", motion:motion, period:period}
    : {level:0, count:count, place:place, matMode:"global", mat:material, motion:motion, period:period};
  var st=SCEN.platform.make(mulberry(seed), K);
  var keyFn=hmaKeyFn(st);
  /* layout: per-phase platform cell map for phases 0..period-1 plus ground material */
  var phases=[];
  for(var p=0;p<period;p++){
    var sp=cloneState(st); sp.tick=p;
    var cells=platCells(sp), entries=[];
    Object.keys(cells).forEach(function(k){ entries.push([k, cells[k]]); });
    entries.sort(function(a,b){
      var pa=a[0].split(","), pb=b[0].split(",");
      return (pa[0]-pb[0]) || (pa[1]-pb[1]);
    });
    phases.push(entries);
  }
  var layout=JSON.stringify({ground:st.groundMat, phases:phases});
  /* successors: full reachable successor relation from the start state via platExpand */
  var seen={}, queue=[st], tripSet={}, triples=[];
  seen[keyFn(st)]=st;
  while(queue.length){
    var cur=queue.shift(), ck=keyFn(cur);
    platExpand(cur).forEach(function(e){
      var tk=keyFn(e.to), id=ck+""+e.label+""+tk;
      if(!tripSet[id]){ tripSet[id]=1; triples.push([ck, e.label, tk]); }
      if(!seen[tk]){ seen[tk]=e.to; queue.push(e.to); }
    });
  }
  triples.sort(function(a,b){
    return a[0]<b[0]?-1:a[0]>b[0]?1 : a[1]<b[1]?-1:a[1]>b[1]?1 : a[2]<b[2]?-1:a[2]>b[2]?1 : 0;
  });
  var successors=JSON.stringify(triples);
  /* plan: frontier candidate set from buildPlans filtered by vecFrontier */
  var cands=SCEN.platform.buildPlans(st);
  var fr=vecFrontier(cands);
  var plan=JSON.stringify(fr.map(function(c){
    return c.steps.map(function(s){ return s.label; });
  }).sort(function(a,b){
    var ja=JSON.stringify(a), jb=JSON.stringify(b);
    return ja<jb?-1:ja>jb?1:0;
  }));
  var ep={st:st, keyFn:keyFn, cands:cands, layout:layout, successors:successors, plan:plan, selCache:{}};
  HMA.physCache[key]=ep;
  return ep;
}
/* selection + execution for one episode under one weight vector */
function hmaSelectExec(ep, W){
  var wkey=W.steps+"|"+W.specials+"|"+W.entropy+"|"+W.slides;
  if(ep.selCache[wkey]) return ep.selCache[wkey];
  var sel=selectPlanW(ep.cands, W);
  var selection= sel ? JSON.stringify(sel.steps.map(function(s){ return s.label; })) : "none";
  var execution;
  if(!sel){
    execution=JSON.stringify({goal:false, end:"none", rev:"vacuous"});
  } else {
    var end= sel.steps.length ? sel.steps[sel.steps.length-1].after : ep.st;
    var goal=!!SCEN.platform.goal(end);
    var cur=end, ok=true;
    for(var i=sel.steps.length-1;i>=0;i--){
      var inv=sel.steps[i].inv, nxt=null, edges=platExpand(cur);
      for(var j=0;j<edges.length;j++){
        if(edges[j].label===inv || edges[j].label.replace(/\+SLIDE\d+$/,"")===inv){ nxt=edges[j].to; break; }
      }
      if(!nxt){ ok=false; break; }
      cur=nxt;
    }
    var rev= (ok && ep.keyFn(cur)===ep.keyFn(ep.st)) ? "pass" : "fail";
    execution=JSON.stringify({goal:goal, end:ep.keyFn(end), rev:rev});
  }
  var out={selection:selection, execution:execution};
  ep.selCache[wkey]=out;
  return out;
}
function hmaBuildInstance(seed, period){
  var contract=hmaContract();
  var behavior={layout:[], successors:[], plan:[], selection:[], execution:[]};
  contract.forEach(function(row){
    var ep=hmaEpisode(row[0], row[1], row[2], row[3], seed, period);
    var se=hmaSelectExec(ep, {steps:row[4], specials:row[5], entropy:row[6], slides:row[7]});
    behavior.layout.push(ep.layout);
    behavior.successors.push(ep.successors);
    behavior.plan.push(ep.plan);
    behavior.selection.push(se.selection);
    behavior.execution.push(se.execution);
  });
  return {
    name:"platform arena · seed "+seed+" · period "+period,
    axes:HMA_AXES.map(function(a){ return {name:a.name, values:a.values.slice()}; }),
    contract:contract,
    components:HMA_COMPS.slice(),
    behavior:behavior,
    hyperedges:HMA_EDGES.map(function(e){ return {components:e.components.slice(), weight:e.weight}; })
  };
}

module.exports = { hmaBuildInstance };
