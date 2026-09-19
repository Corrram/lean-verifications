const base = document.body.dataset.base;
const menu = document.querySelector('.menu-toggle');
const navigation = document.querySelector('#navigation');
menu?.addEventListener('click', () => {
  const open = menu.getAttribute('aria-expanded') !== 'true';
  menu.setAttribute('aria-expanded', String(open));
  navigation.classList.toggle('open', open);
});
document.addEventListener('keydown', (event) => {
  if (event.key === 'Escape' && navigation?.classList.contains('open')) {
    menu.setAttribute('aria-expanded', 'false'); navigation.classList.remove('open'); menu.focus();
  }
  if (event.key === '/' && !event.ctrlKey && !event.metaKey && !event.altKey && !/INPUT|TEXTAREA|SELECT/.test(document.activeElement.tagName) && !document.activeElement.isContentEditable) {
    event.preventDefault();
    const input = document.querySelector('#search-query');
    if (input) input.focus(); else window.location.href = `${base}search/`;
  }
});

const normalize = (text) => text.toLowerCase().normalize('NFKD').replace(/ξ/g, ' xi ').replace(/ρ/g, ' rho ').replace(/β/g, ' beta ').replace(/τ/g, ' tau ').replace(/φ/g, ' phi ').replace(/γ/g, ' gamma ').replace(/[’']/g, '').replace(/[–—_-]/g, ' ');
const filter = document.querySelector('#paper-filter');
const publication = document.querySelector('#publication-filter');
function filterPapers() {
  const words = normalize(filter.value).trim().split(/\s+/).filter(Boolean);
  let visible = 0;
  document.querySelectorAll('.paper-row').forEach((row) => {
    const haystack = normalize(row.dataset.search);
    row.hidden = !(words.every((word) => haystack.includes(word)) && (publication.value === 'all' || publication.value === row.dataset.publication));
    if (!row.hidden) visible++;
  });
  document.querySelector('#paper-count').textContent = `${visible} article${visible === 1 ? '' : 's'}`;
  document.querySelector('#paper-empty').hidden = visible !== 0;
}
filter?.addEventListener('input', filterPapers);
publication?.addEventListener('change', filterPapers);

const searchForm = document.querySelector('#collection-search');
if (searchForm) {
  const input = document.querySelector('#search-query');
  const results = document.querySelector('#search-results');
  const status = document.querySelector('#search-status');
  const native = document.querySelector('#native-search-link');
  let dataPromise;
  let generation = 0;
  let timer;
  async function getData() {
    if (!dataPromise) dataPromise = Promise.allSettled([
      fetch(`${base}search-index.json`).then((r) => { if (!r.ok) throw new Error('Handbook index unavailable'); return r.json(); }),
      fetch(`${base}api/declarations/declaration-data.bmp`).then((r) => { if (!r.ok) throw new Error('Lean index unavailable'); return r.json(); }),
    ]);
    return dataPromise;
  }
  function addResult(item) {
    const article = document.createElement('article'); article.className = 'search-result';
    const kind = document.createElement('small'); kind.textContent = item.kind;
    const a = document.createElement('a'); a.textContent = item.title; a.href = item.url;
    article.append(kind, a);
    if (item.snippet) { const p = document.createElement('p'); p.textContent = item.snippet; article.append(p); }
    results.append(article);
  }
  async function search() {
    const run = ++generation;
    const query = input.value.trim();
    const words = normalize(query).split(/\s+/).filter(Boolean);
    results.replaceChildren();
    native.href = `${base}api/search.html?q=${encodeURIComponent(query)}`;
    const location = new URL(window.location.href);
    if (query) location.searchParams.set('q', query); else location.searchParams.delete('q');
    history.replaceState(null, '', location);
    if (!words.length) { status.textContent = 'Enter a term to search the handbook and generated Lean reference.'; return; }
    status.textContent = 'Loading the handbook and Lean declaration index…';
    const [handbook, lean] = await getData();
    if (run !== generation) return;
    let count = 0;
    if (handbook.status === 'fulfilled') {
      const ranked = handbook.value.map((item) => ({ ...item, score: words.reduce((n, word) => n + (normalize(item.title).includes(word) ? 3 : normalize(item.keywords || '').includes(word) ? 2 : 0), 0) })).filter((item) => words.every((word) => normalize(`${item.title} ${item.text}`).includes(word))).sort((a, b) => b.score - a.score).slice(0, 12);
      for (const item of ranked) { addResult(item); count++; }
    }
    if (lean.status === 'fulfilled') {
      const matches = Object.entries(lean.value.declarations).filter(([name]) => words.every((word) => normalize(name).includes(word))).sort(([a], [b]) => Number(!a.startsWith('ProbabilityTheory.Copula')) - Number(!b.startsWith('ProbabilityTheory.Copula')) || a.length - b.length).slice(0, 15);
      for (const [name, item] of matches) {
        // doc-gen4 emits paths relative to the API root. Only accept local links.
        const dest = new URL(item.docLink.replace(/^\//, ''), new URL(`${base}api/`, window.location.origin));
        if (dest.origin !== window.location.origin || !dest.pathname.startsWith(`${base}api/`)) continue;
        addResult({ title: name, kind: 'Lean declaration', url: dest.href }); count++;
      }
    }
    const unavailable = [handbook.status === 'rejected' && 'handbook', lean.status === 'rejected' && 'Lean'].filter(Boolean);
    status.textContent = `${count ? `Showing ${count} result${count === 1 ? '' : 's'}.` : 'No matches. Try a shorter name or a different term.'}${unavailable.length ? ` The ${unavailable.join(' and ')} index could not be loaded. Reload to retry.` : ' Use the full Lean search for additional declaration results.'}`;
  }
  searchForm.addEventListener('submit', (event) => { event.preventDefault(); clearTimeout(timer); search(); });
  input.addEventListener('input', () => { clearTimeout(timer); generation++; timer = setTimeout(search, 180); });
  input.value = new URL(window.location.href).searchParams.get('q') || '';
  if (input.value) search();
}
