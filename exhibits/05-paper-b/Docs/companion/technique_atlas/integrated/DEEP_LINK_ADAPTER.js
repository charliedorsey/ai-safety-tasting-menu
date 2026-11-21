/* R0007 integration adapter. Does not replace Selvara's original mathematical data or narrative. */
'use strict';
(() => {
  const payload=JSON.parse(document.querySelector('#r0007-concordance').textContent);
  const byId=Object.fromEntries(payload.records.map(r=>[r.id,r]));
  const BIB=payload.bibliography;
  let routing=false;
  const pageLink=(page)=>'../../paper/paper.pdf#page='+page;
  const srcFile=(p)=>'../../source/atlas_pages/'+p.replaceAll('/','__').replace(/\.lean$/,'.html');
  const safe= s=>esc(String(s??''));
  function hashWrite(viewName, subtype, value){
    if(routing) return;
    const qs=new URLSearchParams({view:viewName});
    if(subtype && value) qs.set(subtype,value);
    try{history.replaceState(null,'','#'+qs.toString());}catch(_){location.hash=qs.toString();}
  }
  const originalRenderSources=renderSources;
  renderSources=function(entries){
    return entries.map(orig=>{
      const e={...orig};
      // One corrupt historical endpoint label in original card. Never mutate the original data.
      if(e.path==='GoldC/QuillonLR.lean' && e.line===540 && e.end===645){e.end=629;}
      let base=originalRenderSources([e]);
      let link='';
      if(e.path.endsWith('.lean')){
        const target=srcFile(e.path)+(e.line?'#L'+e.line:'');
        link=`<p class="source-open"><a href="${safe(target)}">Read exact archived source lines ↗</a></p>`;
      }else if(e.path==='paper_b_frozen.canonical.tex'){
        link='<p class="source-open"><a href="../../history/paper_b_frozen.canonical.tex">Read the unchanged historical TeX source ↗</a></p>';
      }
      return `<div class="evidence-wrap">${base}${link}</div>`;
    }).join('');
  };
  function provenance(r){
    if(!r) return '';
    const lit=r.literature_keys.length
      ? r.literature_keys.map(k=>`<a href="references.html#${safe(k)}">${safe(BIB[k]?.[0]||k)}</a>`).join(' · ')
      : '<span>None independently asserted for this exact source-specific identity</span>';
    const src=r.source_first?`<a href="${safe(srcFile(r.source_first))}#L${safe(r.source_line||1)}">${safe(r.source_first)}:${safe(r.source_line||1)}</a>`:'Consult the original archived record';
    const caution=r.id==='CELL-RL'?'<p class="lead-note"><strong>Source-label correction:</strong> Original PASS 6 end line 645 exceeds file length 636; verified theorem ends 629. Corrected label appears here; archived original is unmodified.</p>':'';
    return `<section class="provenance" aria-label="Scholarly citation and provenance for ${safe(r.id)}">
       <div class="kicker">R0007 / scholarly context · ${safe(r.id)}</div>
       <h3>Where this operation comes from—and where it goes.</h3>
       <div class="credit-grid">
        <div class="credit-field"><b>Published mathematical ancestry</b><p>${lit}</p><p>${safe(r.literature_note)}</p></div>
        <div class="credit-field"><b>In the canonical 31-page paper</b><p><a href="${pageLink(r.article_page)}">${safe(r.article_location)} ↗</a></p><p>This is the R0006 mathematical publication cut, not the historical September layout.</p></div>
        <div class="credit-field"><b>Verified formal implementation</b><p>${src}</p><p>SHA-256 <code>${safe(r.source_sha256)}</code></p></div>
        <div class="credit-field"><b>Research-history credit (separate from proofs)</b><p>${safe(r.historical_role)}</p></div>
       </div>${caution}
       <p class="lead-note">A bibliography identifies method ancestry, not a proof of this exact physical application. Source-link verification is not a fresh Lean replay. No personal project attribution is inferred from a file or theorem name.</p>
     </section>`;
  }
  const origChooseCell=chooseCell;
  chooseCell=function(id){
    origChooseCell(id);
    const r=byId['CELL-'+id];
    if(r){document.querySelector('#cellDetail')?.insertAdjacentHTML('beforeend',provenance(r));}
    hashWrite('cells','cell',id);
  };
  const origCardList=cardList;
  cardList=function(){
    origCardList();
    const r=byId[selectedCard];
    if(r){document.querySelector('#cardDetail')?.insertAdjacentHTML('beforeend',provenance(r));}
    if(selectedCard) hashWrite('engines','card',selectedCard);
  };
  const origProofList=proofList;
  proofList=function(){
    origProofList();
    const box=document.querySelector('#proofDetail');
    if(box)box.insertAdjacentHTML('beforeend',`<div class="atlas-bridge"><a href="${pageLink(15)}">Proof meets at the terminal · p. 15 ↗</a><a href="${pageLink(31)}">Source contracts · Appendix H ↗</a></div><p class="lead-note">${safe(selectedProof)} belongs to Selvara's curated 26-edge evidence map, not an exhaustive elaborated Lean dependency graph.</p>`);
    hashWrite('spine','node',selectedProof);
  };
  const origEquationChain=equationChain;
  equationChain=function(){
    origEquationChain();
    hashWrite('euler','lane',lane);
  };
  const origSourceRows=sourceRows;
  sourceRows=function(){
    origSourceRows();
    const term=document.getElementById('sourceSearch').value.toLowerCase().trim();
    const filtered=D.sources.filter(s=>s.path.toLowerCase().includes(term));
    Array.from(document.querySelectorAll('#sourceRows tr')).forEach((tr,i)=>{
      const e=filtered[i];if(!e||!tr.cells.length)return;
      const a=document.createElement('a');a.href=srcFile(e.path)+'#L1';a.textContent=(e.root||'LEAN')+'/'+e.path;
      tr.cells[0].replaceChildren(a);
    });
  };
  const origView=view;
  view=function(v){
    origView(v);
    if(v==='cells') hashWrite(v,'cell',selectedCell);
    else if(v==='engines') hashWrite(v,'card',selectedCard);
    else if(v==='spine') hashWrite(v,'node',selectedProof);
    else if(v==='euler')hashWrite(v,'lane',lane);
    else hashWrite(v);
  };
  // Restore all source links, and append reader-facing context to default initial selections.
  routing=true;
  chooseCell(selectedCell);cardList();proofList();equationChain();sourceRows();
  routing=false;
  const addBridge=(which,content)=>{const area=document.getElementById('view-'+which);area?.insertAdjacentHTML('afterbegin',content);};
  addBridge('overview',`<div class="atlas-summary"><strong>Selvara / FACET — Pass 6 source archaeology · 23 October 2026.</strong> This lighter R0007 presentation retains the complete 62-card atlas. R0006 is the 31-page canonical paper, with separate literary history and a human author-release gate. The only corrected source-span metadata is CELL-RL's 540–629 endpoint; see the preserved original for the unmodified record.<div class="atlas-bridge"><a class="primary" href="../../paper/paper.pdf">Read the mathematical paper ↗</a><a href="../reading_room/index.html">Five guided mechanisms ↗</a><a href="references.html">Bibliography and contributor-credit policy ↗</a></div></div>`);
  addBridge('budgets',`<div class="atlas-summary"><strong>Reading the source budget.</strong> The graph preserves Selvara's 41 quantitative nodes and typed transitions. The displayed source exponents and bounds are mathematics, not algorithmic estimates of software runtime. <a href="${pageLink(30)}">Appendix G · sector budgets ↗</a></div>`);
  addBridge('euler',`<div class="atlas-summary"><strong>25 exact Euler equation transitions.</strong> Switch among A, B, Dictionary and Both to inspect their recorded algebra. Matching printed identities: <a href="${pageLink(6)}">§4 ↗</a> and <a href="${pageLink(27)}">Appendix E ↗</a>. Classical-method attribution is indexed separately in <a href="references.html">citations and credits</a>.</div>`);
  addBridge('sources',`<div class="atlas-summary"><strong>70 checked original source files.</strong> Every file hash matches the sealed R0003 source. Each row opens a private source viewer at original line numbers. The source viewer is not licensed for automatic public redistribution and this atlas is not a full clean Lean replay.</div>`);
  addBridge('cells',`<div class="atlas-summary"><strong>All twelve cells have six original Selvara trace steps.</strong> Select a cell to see the exact eligibility mask, method, local costs, physical rate, aggregation and terminal transport. The new scholarly context is appended <em>after</em> her original trace; it does not replace it.</div>`);
  addBridge('engines',`<div class="atlas-summary"><strong>62 untouched mathematical records.</strong> Filter, search, and select; each card now ends with a separate R0007 classical-antecedent / formal-source / paper-location / historical-credit overlay. No card is rewritten or newly attributed from its source filename alone.</div>`);
  function route(){
    let h=location.hash.slice(1);if(!h)return;
    let p=new URLSearchParams(h);let v=p.get('view');
    if(!['overview','spine','cells','budgets','engines','euler','sources'].includes(v))return;
    routing=true;
    try{
      if(v==='cells'){
        const c=p.get('cell');if(c&&D.cells.some(x=>x.cell===c))chooseCell(c);
      }else if(v==='engines'){
        const c=p.get('card');if(c&&cardby[c]){
          document.getElementById('cardSearch').value='';document.getElementById('cardFamily').value='all';
          selectedCard=c;cardList();
        }
      }else if(v==='spine'){
        const n=p.get('node');if(n&&sid[n]){selectedProof=n;document.getElementById('proofFilter').value='all';proofList();}
      }else if(v==='euler'){
        const l=p.get('lane');if(['A','B','Dictionary','Both'].includes(l)){lane=l;equationChain();}
      }
      view(v);
    }finally{routing=false;}
  }
  window.addEventListener('hashchange',route);
  route();
  window.__paperBAtlasR0007={counts:{views:7,cards:62,cells:12,transitions:25,proofEdges:26,budgetNodes:41},getSelection:()=>({view:current,card:selectedCard,cell:selectedCell})};
})();
