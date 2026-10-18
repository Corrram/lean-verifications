(() => {
  'use strict';
  const metadata = JSON.parse(document.getElementById('reader-metadata').textContent);
  const paper = document.getElementById('reader-paper');
  const inspector = document.querySelector('.reader-inspector');
  const title = document.getElementById('reader-inspector-title');
  const mathPanel = document.getElementById('reader-math-panel');
  const evidencePanel = document.getElementById('reader-evidence-panel');
  const tabs = [...document.querySelectorAll('.reader-tabs [role="tab"]')];
  let selected = null, returnFocus = null;
  const evidenceFor = block => [...block.children].find(e => e.matches('details.article-evidence'));
  const appendTemplate = (target, id) => target.append(document.getElementById(id).content.cloneNode(true));
  const paragraph = (text, className='') => { const p=document.createElement('p'); p.textContent=text;p.className=className;return p; };
  const clone = node => {
    const copy=node.cloneNode(true);
    copy.removeAttribute('id');
    copy.querySelectorAll('[id]').forEach(n=>n.removeAttribute('id'));
    copy.querySelectorAll('.article-evidence').forEach(n=>n.remove());
    return copy;
  };
  function selectTab(index, focus=false) {
    tabs.forEach((tab,i)=>{tab.setAttribute('aria-selected',String(i===index));tab.tabIndex=i===index?0:-1;});
    mathPanel.hidden=index!==0;evidencePanel.hidden=index!==1;
    if(focus)tabs[index].focus();
  }
  function open(label, trigger) {
    if(trigger&&!inspector.contains(trigger))returnFocus=trigger;
    title.textContent=label;
    mathPanel.replaceChildren();evidencePanel.replaceChildren();
    inspector.hidden=false;document.body.classList.add('companion-open');
    document.querySelectorAll('[data-view]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.view==='companion')));
    selectTab(0);document.querySelector('.reader-inspector-scroll').scrollTop=0;
  }
  function mark(block) {
    selected?.classList.remove('reader-selected');
    selected=block;selected?.classList.add('reader-selected');
    paper.querySelectorAll('.article-evidence>summary').forEach(s=>s.setAttribute('aria-expanded',String(s.parentElement.parentElement===block)));
  }
  function close() {
    inspector.hidden=true;document.body.classList.remove('companion-open');mark(null);
    document.querySelectorAll('[data-view]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.view==='article')));
    if(returnFocus?.isConnected)returnFocus.focus({preventScroll:true});
  }
  function sourceDetails(block, info, evidence) {
    evidencePanel.append(paragraph('Compiled counterparts', 'reader-status'));
    evidencePanel.append(paragraph('These are the actual theorem types attached to this passage. A link does not certify the wording of the original article.', 'reader-small'));
    if(evidence) {
      const native=evidence.querySelector('.article-native-types');
      const records=native?[...native.children].filter(e=>e.tagName!=='SUMMARY'):[...evidence.children].filter(e=>e.tagName==='SECTION'&&!e.classList.contains('article-checked-calculation'));
      for(const record of records) {
        const details=document.createElement('details');details.className='reader-technical';
        const summary=document.createElement('summary');
        const name=record.querySelector('p a')?.textContent ?? 'Lean statement';
        summary.textContent=name.split('.').slice(-1)[0];
        details.append(summary,clone(record));evidencePanel.append(details);
      }
    }
    if(info?.latex) {
      const details=document.createElement('details');details.className='reader-technical';
      const summary=document.createElement('summary');summary.textContent='Exact original LaTeX';
      const pre=document.createElement('pre');pre.textContent=info.latex;
      details.append(summary,pre);evidencePanel.append(details);
    }
    const back=document.createElement('a');back.href='#'+block.id;back.dataset.returnToArticle='';back.textContent='Locate in the article ↗';
    evidencePanel.append(back);
  }
  function showPassage(block, trigger) {
    const info=metadata.passages[block.dataset.passage];
    const evidence=evidenceFor(block);
    const label=info?.label??block.querySelector('h3,h4')?.textContent??'Definition in the article';
    open(label,trigger);mark(block);
    const definitionKey=metadata.definitionKeys[block.id];
    const definitionTemplate=[...document.querySelectorAll('template[data-definition]')].find(t=>t.dataset.definition===definitionKey);
    if(definitionTemplate) mathPanel.append(definitionTemplate.content.cloneNode(true));
    else if(info?.corollary) appendTemplate(mathPanel,'reader-corollary');
    else if(evidence?.querySelector('.article-checked-calculation')) {
      mathPanel.append(paragraph('Mathematical proof steps checked','reader-status'));
      evidence.querySelectorAll('.article-checked-calculation').forEach(n=>mathPanel.append(clone(n)));
      mathPanel.append(paragraph('The checked proof document is shown here. The original wording remains in the article.','reader-small'));
    } else {
      mathPanel.append(paragraph(evidence?'Original formulation · Lean counterparts available':'Original formulation','reader-status'));
      const original=clone(block);original.classList.add('reader-excerpt');mathPanel.append(original);
      mathPanel.append(paragraph('A precise source-checked companion for this passage has not yet been added. Inspect its existing formal statements under “Lean & source”.','reader-small'));
      const button=document.createElement('button');button.className='reader-inline-button';button.textContent='Inspect formal statements →';button.addEventListener('click',()=>selectTab(1,true));mathPanel.append(button);
    }
    sourceDetails(block,info,evidence);
  }
  function definition(key, trigger) {
    const template=[...document.querySelectorAll('template[data-definition]')].find(t=>t.dataset.definition===key);
    if(!template)return false;
    open(template.dataset.title,trigger);
    if(selected) {
      const origin=selected;
      const back=document.createElement('button');back.type='button';back.className='reader-back';
      back.textContent='← '+(metadata.passages[origin.dataset.passage]?.label??'Article passage');
      back.addEventListener('click',()=>showPassage(origin,back));mathPanel.append(back);
    }
    mathPanel.append(template.content.cloneNode(true));
    evidencePanel.append(paragraph('Definition correspondence','reader-status'));
    const technical=mathPanel.querySelector('.reader-technical');
    if(technical)evidencePanel.append(technical.cloneNode(true));
    evidencePanel.append(paragraph('This definition is part of the existing checked mathematical companion. Its literal LaTeX source has not yet been checked by the new source engine.','reader-small'));
    return true;
  }
  function welcome(trigger) {
    open('Alongside the article',trigger);mark(null);appendTemplate(mathPanel,'reader-welcome');appendTemplate(evidencePanel,'reader-scope');
  }
  function scope(trigger) {
    open('What is verified',trigger);mark(null);appendTemplate(mathPanel,'reader-scope');appendTemplate(evidencePanel,'reader-scope');
  }
  // Progressive enhancement: without this script the original details remain
  // usable inline. With it, only the small marker occupies the paper's margin.
  paper.querySelectorAll('.article-evidence').forEach(evidence=>{
    const summary=evidence.querySelector(':scope > summary');
    const block=evidence.parentElement,info=metadata.passages[block.dataset.passage];
    const precise=info?.corollary||metadata.definitionKeys[block.id]||!!evidence.querySelector('.article-checked-calculation');
    summary.textContent=precise?'Companion':'Lean';
    summary.classList.toggle('reader-precise-marker',precise);
    summary.setAttribute('aria-label',`${precise?'Open mathematical companion':'Inspect Lean counterparts'}: ${info?.label??'article passage'}`);
    summary.setAttribute('aria-controls','reader-math-panel');summary.setAttribute('aria-expanded','false');
    summary.title=precise?'Open the checked mathematical companion':'View compiled counterparts; exact source not yet certified';
    summary.addEventListener('click',event=>{event.preventDefault();showPassage(block,summary);});
    evidence.open=false;
  });
  document.querySelector('.article-bibliography').id='reader-references';
  document.body.classList.add('reader-enhanced');
  document.querySelector('.reader-close').addEventListener('click',close);
  document.querySelectorAll('[data-view]').forEach(button=>button.addEventListener('click',()=>button.dataset.view==='article'?close():welcome(button)));
  document.querySelectorAll('[data-open-scope]').forEach(button=>button.addEventListener('click',()=>scope(button)));
  tabs.forEach((tab,index)=>{
    tab.addEventListener('click',()=>selectTab(index));
    tab.addEventListener('keydown',e=>{if(['ArrowLeft','ArrowRight','Home','End'].includes(e.key)){e.preventDefault();selectTab(e.key==='Home'?0:e.key==='End'?1:1-index,true);}});
  });
  document.addEventListener('keydown',e=>{if(e.key==='Escape'&&!inspector.hidden){close();e.preventDefault();}});
  document.addEventListener('click',event=>{
    const shortcut=event.target.closest('[data-select]');
    if(shortcut) {
      const block=document.getElementById(shortcut.dataset.select);
      if(block){showPassage(block,shortcut);block.scrollIntoView({block:'start'});}return;
    }
    const link=event.target.closest('a[href^="#"]');
    if(!link)return;
    const id=link.getAttribute('href').slice(1);
    if(link.hasAttribute('data-return-to-article')) {event.preventDefault();document.getElementById(id)?.scrollIntoView({block:'center'});return;}
    if(id.startsWith('def-')&&definition(id.slice(4),link)){event.preventDefault();return;}
    // Only notation links open a definition. Ordinary cross-references retain
    // their original jump behavior and are never mistaken for verification.
    if(link.closest('.katex')&&id.startsWith('article-')) {
      const block=document.getElementById(id);
      if(block){event.preventDefault();showPassage(block,link);}
    }
  });
  // Keep original section anchors and browser history behavior for the outline.
  const outlineLinks=[...document.querySelectorAll('.reader-outline a[href^="#"]')];
  const sections=outlineLinks.map(a=>document.getElementById(a.getAttribute('href').slice(1))).filter(Boolean);
  let ticking=false;
  function position() {
    let current=sections[0];
    for(const section of sections)if(section.getBoundingClientRect().top<180)current=section;
    outlineLinks.forEach(a=>{if(a.hash==='#'+current?.id)a.setAttribute('aria-current','location');else a.removeAttribute('aria-current');});
    ticking=false;
  }
  window.addEventListener('scroll',()=>{if(!ticking){requestAnimationFrame(position);ticking=true;}},{passive:true});position();
})();
