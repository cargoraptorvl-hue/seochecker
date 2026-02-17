import React, { useState, useEffect, useMemo, useRef } from 'react';
import { createRoot } from 'react-dom/client';

// --- ICONS (Inline SVGs for reliability) ---
const Icons = {
  Activity: (props: any) => <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" {...props}><path d="M22 12h-4l-3 9L9 3l-3 9H2"/></svg>,
  AlertCircle: (props: any) => <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" {...props}><circle cx="12" cy="12" r="10"/><line x1="12" x2="12" y1="8" y2="12"/><line x1="12" x2="12.01" y1="16" y2="16"/></svg>,
  AlertTriangle: (props: any) => <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" {...props}><path d="m21.73 18-8-14a2 2 0 0 0-3.48 0l-8 14A2 2 0 0 0 4 21h16a2 2 0 0 0 1.73-3Z"/><line x1="12" x2="12" y1="9" y2="13"/><line x1="12" x2="12.01" y1="17" y2="17"/></svg>,
  CheckCircle: (props: any) => <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" {...props}><path d="M22 11.08V12a10 10 0 1 1-5.93-9.14"/><polyline points="22 4 12 14.01 9 11.01"/></svg>,
  ChevronRight: (props: any) => <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" {...props}><path d="m9 18 6-6-6-6"/></svg>,
  FileText: (props: any) => <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" {...props}><path d="M14.5 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V7.5L14.5 2z"/><polyline points="14 2 14 8 20 8"/></svg>,
  Globe: (props: any) => <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" {...props}><circle cx="12" cy="12" r="10"/><line x1="2" x2="22" y1="12" y2="12"/><path d="M12 2a15.3 15.3 0 0 1 4 10 15.3 15.3 0 0 1-4 10 15.3 15.3 0 0 1-4-10 15.3 15.3 0 0 1 4-10z"/></svg>,
  Layout: (props: any) => <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" {...props}><rect width="18" height="18" x="3" y="3" rx="2" ry="2"/><line x1="3" x2="21" y1="9" y2="9"/><line x1="9" x2="9" y1="21" y2="9"/></svg>,
  Link: (props: any) => <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" {...props}><path d="M10 13a5 5 0 0 0 7.54.54l3-3a5 5 0 0 0-7.07-7.07l-1.72 1.71"/><path d="M14 11a5 5 0 0 0-7.54-.54l-3 3a5 5 0 0 0 7.07 7.07l1.71-1.71"/></svg>,
  Play: (props: any) => <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" {...props}><polygon points="5 3 19 12 5 21 5 3"/></svg>,
  Search: (props: any) => <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" {...props}><circle cx="11" cy="11" r="8"/><line x1="21" x2="16.65" y1="21" y2="16.65"/></svg>,
  Settings: (props: any) => <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" {...props}><path d="M12.22 2h-.44a2 2 0 0 0-2 2v.18a2 2 0 0 1-1 1.73l-.43.25a2 2 0 0 1-2 0l-.15-.08a2 2 0 0 0-2.73.73l-.22.38a2 2 0 0 0 .73 2.73l.15.1a2 2 0 0 1 1 1.72v.51a2 2 0 0 1-1 1.74l-.15.09a2 2 0 0 0-.73 2.73l.22.38a2 2 0 0 0 2.73.73l.15-.08a2 2 0 0 1 2 0l.43.25a2 2 0 0 1 1 1.73V20a2 2 0 0 0 2 2h.44a2 2 0 0 0 2-2v-.18a2 2 0 0 1 1-1.73l.43-.25a2 2 0 0 1 2 0l.15.08a2 2 0 0 0 2.73-.73l.22-.39a2 2 0 0 0-.73-2.73l-.15-.1a2 2 0 0 1-1-1.72v-.51a2 2 0 0 1 1-1.74l.15-.09a2 2 0 0 0 .73-2.73l-.22-.38a2 2 0 0 0-2.73-.73l-.15.08a2 2 0 0 1-2 0l-.43-.25a2 2 0 0 1-1-1.73V4a2 2 0 0 0-2-2z"/><circle cx="12" cy="12" r="3"/></svg>,
  Zap: (props: any) => <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" {...props}><polygon points="13 2 3 14 12 14 11 22 21 10 12 10 13 2"/></svg>,
};

// --- TYPES ---

type Severity = 'critical' | 'warning' | 'info' | 'success';

interface Issue {
  id: string;
  type: Severity;
  category: string;
  message: string;
}

interface PageData {
  url: string;
  statusCode: number;
  ttfb: number;
  title: string;
  wordCount: number;
  issues: Issue[];
}

interface ScanStats {
  pagesScanned: number;
  totalPages: number;
  currentUrl: string;
  duration: number;
  isScanning: boolean;
  progress: number;
  logs: string[];
}

// --- UTILS & SIMULATION ---

const generateFakePages = (domain: string, maxPages: number): PageData[] => {
  const pages: PageData[] = [];
  const paths = [
    '', 'about', 'contact', 'services', 'blog', 'blog/post-1', 'blog/post-2', 
    'products', 'products/item-a', 'products/item-b', 'faq', 'terms', 'privacy'
  ];
  
  // Extend paths if needed
  while (paths.length < maxPages) {
    paths.push(`page-${paths.length}`);
  }

  const issuesLibrary = [
    { type: 'critical', category: 'technical', message: 'Missing Title Tag' },
    { type: 'critical', category: 'technical', message: '404 Not Found' },
    { type: 'critical', category: 'performance', message: 'Slow Server Response (>3s)' },
    { type: 'warning', category: 'content', message: 'Missing H1 Header' },
    { type: 'warning', category: 'content', message: 'Low Word Count (<300 words)' },
    { type: 'warning', category: 'seo', message: 'Meta Description too short' },
    { type: 'info', category: 'seo', message: 'Missing Open Graph Tags' },
    { type: 'info', category: 'technical', message: 'Non-canonical URL' },
  ] as const;

  for (let i = 0; i < maxPages; i++) {
    const path = paths[i % paths.length] + (i >= paths.length ? `-${i}` : '');
    const isError = Math.random() < 0.1;
    const statusCode = isError ? (Math.random() < 0.5 ? 404 : 500) : 200;
    const ttfb = Math.random() * 2.0 + (Math.random() < 0.1 ? 2.0 : 0); // Occasional slow page

    const pageIssues: Issue[] = [];
    
    if (statusCode !== 200) {
      pageIssues.push({ id: `iss-${i}-1`, type: 'critical', category: 'technical', message: `Status Code: ${statusCode}` });
    } else {
      // Random issues
      if (Math.random() < 0.15) pageIssues.push({ ...issuesLibrary[0], id: `iss-${i}-0` });
      if (Math.random() < 0.2) pageIssues.push({ ...issuesLibrary[3], id: `iss-${i}-3` });
      if (Math.random() < 0.25 && ttfb > 1.0) pageIssues.push({ ...issuesLibrary[2], id: `iss-${i}-2` });
      if (Math.random() < 0.3) pageIssues.push({ ...issuesLibrary[4], id: `iss-${i}-4` });
    }

    pages.push({
      url: `${domain.replace(/\/$/, '')}/${path}`,
      statusCode,
      ttfb,
      title: path ? `${path.charAt(0).toUpperCase() + path.slice(1)} - ${domain}` : `Home - ${domain}`,
      wordCount: Math.floor(Math.random() * 2000) + 100,
      issues: pageIssues
    });
  }
  return pages;
};

// --- COMPONENTS ---

const Badge = ({ type, children }: { type: Severity; children?: React.ReactNode }) => {
  const colors = {
    critical: 'bg-red-500/10 text-red-400 border-red-500/20',
    warning: 'bg-amber-500/10 text-amber-400 border-amber-500/20',
    info: 'bg-blue-500/10 text-blue-400 border-blue-500/20',
    success: 'bg-emerald-500/10 text-emerald-400 border-emerald-500/20',
  };
  return (
    <span className={`px-2 py-0.5 rounded text-xs font-medium border ${colors[type]}`}>
      {children}
    </span>
  );
};

const ScoreCircle = ({ score }: { score: number }) => {
  const circumference = 2 * Math.PI * 40;
  const offset = circumference - (score / 100) * circumference;
  
  let color = 'text-red-500';
  if (score > 50) color = 'text-amber-500';
  if (score > 80) color = 'text-emerald-500';

  return (
    <div className="relative flex items-center justify-center w-32 h-32">
      <svg className="w-full h-full transform -rotate-90">
        <circle cx="64" cy="64" r="40" stroke="currentColor" strokeWidth="8" fill="transparent" className="text-slate-800" />
        <circle cx="64" cy="64" r="40" stroke="currentColor" strokeWidth="8" fill="transparent"
          strokeDasharray={circumference} strokeDashoffset={offset}
          strokeLinecap="round"
          className={`transition-all duration-1000 ease-out ${color}`} />
      </svg>
      <div className="absolute flex flex-col items-center">
        <span className="text-3xl font-bold text-white">{score}</span>
        <span className="text-xs text-slate-400">HEALTH</span>
      </div>
    </div>
  );
};

// --- MAIN APP ---

const App = () => {
  const [view, setView] = useState<'idle' | 'scanning' | 'results'>('idle');
  const [config, setConfig] = useState({ url: '', maxPages: 50, depth: 3 });
  const [stats, setStats] = useState<ScanStats>({
    pagesScanned: 0, totalPages: 0, currentUrl: '', duration: 0, isScanning: false, progress: 0, logs: []
  });
  const [results, setResults] = useState<PageData[]>([]);

  // Simulation Logic
  useEffect(() => {
    if (view === 'scanning') {
      let scanned = 0;
      const total = config.maxPages;
      const fakeData = generateFakePages(config.url, total);
      const startTime = Date.now();
      
      const interval = setInterval(() => {
        scanned++;
        const currentData = fakeData[scanned - 1];
        
        setStats(prev => ({
          ...prev,
          pagesScanned: scanned,
          totalPages: total,
          currentUrl: currentData?.url || '',
          duration: (Date.now() - startTime) / 1000,
          progress: (scanned / total) * 100,
          logs: [...prev.logs, `${currentData?.statusCode === 200 ? '✅' : '🔴'} ${currentData?.statusCode} ${currentData?.url}`].slice(-10)
        }));

        if (scanned >= total) {
          clearInterval(interval);
          setResults(fakeData);
          setTimeout(() => setView('results'), 800);
        }
      }, 150); // Speed of simulation

      return () => clearInterval(interval);
    }
  }, [view, config]);

  const startScan = () => {
    if (!config.url) return;
    let url = config.url;
    if (!url.startsWith('http')) url = 'https://' + url;
    setConfig({ ...config, url });
    setStats({ pagesScanned: 0, totalPages: config.maxPages, currentUrl: '', duration: 0, isScanning: true, progress: 0, logs: [] });
    setView('scanning');
  };

  const reset = () => {
    setView('idle');
    setResults([]);
  };

  return (
    <div className="flex h-screen overflow-hidden bg-slate-950 text-slate-50 font-sans">
      {/* SIDEBAR */}
      <aside className="w-72 bg-slate-900 border-r border-slate-800 flex flex-col z-20">
        <div className="p-6 border-b border-slate-800 flex items-center gap-3">
          <div className="bg-indigo-600 p-2 rounded-lg">
            <Icons.Activity className="w-5 h-5 text-white" />
          </div>
          <span className="font-bold text-lg tracking-tight">SEO Audit</span>
        </div>

        <div className="p-6 flex-1 overflow-y-auto">
          <div className="space-y-6">
            <div>
              <label className="block text-xs font-semibold text-slate-400 uppercase tracking-wider mb-2">Target URL</label>
              <div className="relative">
                <Icons.Globe className="absolute left-3 top-3 w-4 h-4 text-slate-500" />
                <input 
                  type="text" 
                  value={config.url}
                  onChange={(e) => setConfig({...config, url: e.target.value})}
                  placeholder="example.com"
                  className="w-full bg-slate-950 border border-slate-700 rounded-lg py-2.5 pl-10 pr-4 text-sm focus:ring-2 focus:ring-indigo-500 focus:border-transparent outline-none transition-all placeholder-slate-600"
                />
              </div>
            </div>

            <div>
              <label className="block text-xs font-semibold text-slate-400 uppercase tracking-wider mb-4">Configuration</label>
              
              <div className="space-y-4">
                <div>
                  <div className="flex justify-between text-sm mb-1">
                    <span className="text-slate-300">Max Pages</span>
                    <span className="text-indigo-400 font-mono">{config.maxPages}</span>
                  </div>
                  <input 
                    type="range" min="10" max="200" step="10"
                    value={config.maxPages}
                    onChange={(e) => setConfig({...config, maxPages: parseInt(e.target.value)})}
                    className="w-full h-1.5 bg-slate-800 rounded-lg appearance-none cursor-pointer accent-indigo-500"
                  />
                </div>

                <div>
                  <div className="flex justify-between text-sm mb-1">
                    <span className="text-slate-300">Crawl Depth</span>
                    <span className="text-indigo-400 font-mono">{config.depth}</span>
                  </div>
                  <input 
                    type="range" min="1" max="10"
                    value={config.depth}
                    onChange={(e) => setConfig({...config, depth: parseInt(e.target.value)})}
                    className="w-full h-1.5 bg-slate-800 rounded-lg appearance-none cursor-pointer accent-indigo-500"
                  />
                </div>
              </div>
            </div>

            <button 
              onClick={view === 'idle' || view === 'results' ? startScan : undefined}
              disabled={view === 'scanning' || !config.url}
              className={`w-full py-3 px-4 rounded-lg font-semibold flex items-center justify-center gap-2 transition-all ${
                view === 'scanning' || !config.url
                  ? 'bg-slate-800 text-slate-500 cursor-not-allowed'
                  : 'bg-indigo-600 hover:bg-indigo-500 text-white shadow-lg shadow-indigo-500/20'
              }`}
            >
              {view === 'scanning' ? (
                <>
                  <div className="animate-spin rounded-full h-4 w-4 border-2 border-white/20 border-t-white"></div>
                  Scanning...
                </>
              ) : (
                <>
                  <Icons.Play className="w-4 h-4" />
                  Start Audit
                </>
              )}
            </button>
            
            {view === 'results' && (
              <button onClick={reset} className="w-full py-2 px-4 rounded-lg border border-slate-700 hover:bg-slate-800 text-slate-400 text-sm transition-colors">
                New Audit
              </button>
            )}
          </div>
        </div>
        
        <div className="p-4 border-t border-slate-800">
           <div className="text-xs text-slate-500 text-center">
             v1.2.0 • Pro Edition
           </div>
        </div>
      </aside>

      {/* MAIN CONTENT */}
      <main className="flex-1 overflow-y-auto relative bg-slate-950">
        {view === 'idle' && <HeroSection />}
        {view === 'scanning' && <ScanningView stats={stats} />}
        {view === 'results' && <ResultsDashboard results={results} duration={stats.duration} />}
      </main>
    </div>
  );
};

const HeroSection = () => (
  <div className="h-full flex flex-col items-center justify-center p-8 text-center animate-fade-in">
    <div className="w-24 h-24 bg-slate-900 rounded-2xl border border-slate-800 flex items-center justify-center mb-8 shadow-2xl">
      <Icons.Search className="w-10 h-10 text-indigo-500" />
    </div>
    <h1 className="text-4xl md:text-5xl font-bold bg-gradient-to-r from-white to-slate-400 bg-clip-text text-transparent mb-4">
      SEO Audit Machine
    </h1>
    <p className="text-lg text-slate-400 max-w-xl mb-12 leading-relaxed">
      Enter your website URL in the sidebar to generate a comprehensive technical SEO analysis, simulating a deep crawl of your site structure.
    </p>
    
    <div className="grid grid-cols-1 md:grid-cols-3 gap-6 max-w-4xl w-full">
      {[
        { icon: Icons.Zap, title: 'Speed Analysis', desc: 'TTFB & Core Vitals checks' },
        { icon: Icons.Layout, title: 'Content Quality', desc: 'Structure, H1s & Metadata' },
        { icon: Icons.Link, title: 'Link Health', desc: 'Broken links & Redirects' },
      ].map((card, i) => (
        <div key={i} className="bg-slate-900/50 border border-slate-800 p-6 rounded-xl hover:bg-slate-900 transition-colors text-left group">
          <card.icon className="w-8 h-8 text-indigo-500 mb-4 group-hover:scale-110 transition-transform" />
          <h3 className="font-semibold text-white mb-2">{card.title}</h3>
          <p className="text-sm text-slate-400">{card.desc}</p>
        </div>
      ))}
    </div>
  </div>
);

const ScanningView = ({ stats }: { stats: ScanStats }) => (
  <div className="h-full flex flex-col items-center justify-center p-12 max-w-3xl mx-auto">
    <div className="w-full mb-12">
      <div className="flex justify-between items-end mb-4">
        <div>
          <h2 className="text-2xl font-bold text-white mb-1">Crawling Website</h2>
          <p className="text-slate-400 text-sm font-mono truncate max-w-md">{stats.currentUrl || 'Initializing...'}</p>
        </div>
        <div className="text-right">
          <span className="text-3xl font-bold text-indigo-500">{Math.round(stats.progress)}%</span>
          <p className="text-xs text-slate-500 uppercase tracking-wider">Completed</p>
        </div>
      </div>
      <div className="h-3 bg-slate-800 rounded-full overflow-hidden">
        <div 
          className="h-full bg-indigo-500 transition-all duration-300 ease-out relative"
          style={{ width: `${stats.progress}%` }}
        >
          <div className="absolute inset-0 bg-white/20 animate-pulse"></div>
        </div>
      </div>
    </div>

    <div className="w-full bg-slate-900 rounded-xl border border-slate-800 overflow-hidden shadow-2xl">
      <div className="bg-slate-800/50 px-4 py-3 border-b border-slate-800 flex justify-between items-center">
        <span className="text-xs font-semibold text-slate-400 uppercase tracking-wider">Live Crawler Logs</span>
        <div className="flex gap-2">
          <div className="w-2.5 h-2.5 rounded-full bg-red-500/50"></div>
          <div className="w-2.5 h-2.5 rounded-full bg-amber-500/50"></div>
          <div className="w-2.5 h-2.5 rounded-full bg-emerald-500/50"></div>
        </div>
      </div>
      <div className="p-4 font-mono text-sm space-y-2 h-64 overflow-hidden flex flex-col justify-end">
        {stats.logs.map((log, i) => (
          <div key={i} className="animate-slide-up opacity-0" style={{ animation: 'slideUp 0.3s forwards' }}>
            {log}
          </div>
        ))}
      </div>
    </div>
  </div>
);

const ResultsDashboard = ({ results, duration }: { results: PageData[], duration: number }) => {
  const [activeTab, setActiveTab] = useState<'overview' | 'issues' | 'pages'>('overview');
  
  // Computed Stats
  const totalPages = results.length;
  const criticalErrors = results.reduce((acc, p) => acc + p.issues.filter(i => i.type === 'critical').length, 0);
  const avgTTFB = results.reduce((acc, p) => acc + p.ttfb, 0) / totalPages;
  const score = Math.max(0, Math.round(100 - (criticalErrors * 5 + results.reduce((acc,p) => acc + p.issues.filter(i => i.type === 'warning').length, 0) * 2) / Math.max(1, totalPages/5)));

  // Group Issues
  const groupedIssues = useMemo(() => {
    const map = new Map<string, { title: string; count: number; type: Severity; urls: string[] }>();
    results.forEach(p => {
      p.issues.forEach(i => {
        if (!map.has(i.message)) {
          map.set(i.message, { title: i.message, count: 0, type: i.type, urls: [] });
        }
        const entry = map.get(i.message)!;
        entry.count++;
        entry.urls.push(p.url);
      });
    });
    return Array.from(map.values()).sort((a, b) => {
      const severityWeight = { critical: 3, warning: 2, info: 1, success: 0 };
      return severityWeight[b.type] - severityWeight[a.type];
    });
  }, [results]);

  return (
    <div className="p-8 max-w-7xl mx-auto animate-fade-in">
      {/* HEADER STATS */}
      <div className="grid grid-cols-1 lg:grid-cols-4 gap-6 mb-8">
        <div className="lg:col-span-1 bg-slate-900 rounded-xl p-6 border border-slate-800 flex items-center justify-between">
          <ScoreCircle score={score} />
        </div>
        
        <div className="lg:col-span-3 grid grid-cols-1 md:grid-cols-3 gap-6">
          <div className="bg-slate-900 rounded-xl p-6 border border-slate-800 relative overflow-hidden group">
            <div className="absolute top-0 right-0 p-4 opacity-10 group-hover:opacity-20 transition-opacity">
               <Icons.FileText className="w-20 h-20 text-blue-500" />
            </div>
            <h3 className="text-slate-400 text-sm font-medium mb-1">Total Pages</h3>
            <p className="text-3xl font-bold text-white">{totalPages}</p>
            <p className="text-xs text-slate-500 mt-2">Scanned in {duration.toFixed(1)}s</p>
          </div>
          
          <div className="bg-slate-900 rounded-xl p-6 border border-slate-800 relative overflow-hidden group">
            <div className="absolute top-0 right-0 p-4 opacity-10 group-hover:opacity-20 transition-opacity">
               <Icons.AlertTriangle className="w-20 h-20 text-red-500" />
            </div>
            <h3 className="text-slate-400 text-sm font-medium mb-1">Critical Issues</h3>
            <p className="text-3xl font-bold text-red-500">{criticalErrors}</p>
            <p className="text-xs text-slate-500 mt-2">Requires immediate attention</p>
          </div>

          <div className="bg-slate-900 rounded-xl p-6 border border-slate-800 relative overflow-hidden group">
             <div className="absolute top-0 right-0 p-4 opacity-10 group-hover:opacity-20 transition-opacity">
               <Icons.Zap className="w-20 h-20 text-amber-500" />
            </div>
            <h3 className="text-slate-400 text-sm font-medium mb-1">Avg. TTFB</h3>
            <p className={`text-3xl font-bold ${avgTTFB > 1.0 ? 'text-amber-500' : 'text-emerald-500'}`}>
              {avgTTFB.toFixed(2)}s
            </p>
            <p className="text-xs text-slate-500 mt-2">Target: &lt; 0.8s</p>
          </div>
        </div>
      </div>

      {/* TABS */}
      <div className="flex border-b border-slate-800 mb-6">
        {['overview', 'issues', 'pages'].map((tab) => (
          <button
            key={tab}
            onClick={() => setActiveTab(tab as any)}
            className={`px-6 py-3 text-sm font-medium capitalize transition-colors border-b-2 ${
              activeTab === tab 
                ? 'border-indigo-500 text-white' 
                : 'border-transparent text-slate-400 hover:text-slate-200'
            }`}
          >
            {tab}
          </button>
        ))}
      </div>

      {/* CONTENT */}
      <div className="min-h-[400px]">
        {activeTab === 'overview' && (
          <div className="space-y-6">
            <h3 className="text-xl font-bold text-white">Action Plan</h3>
            <div className="grid gap-4">
              {groupedIssues.length === 0 ? (
                <div className="p-8 text-center bg-slate-900 rounded-xl border border-slate-800 border-dashed text-slate-400">
                  <Icons.CheckCircle className="w-12 h-12 text-emerald-500 mx-auto mb-3" />
                  <p>No issues found. Great job!</p>
                </div>
              ) : (
                groupedIssues.map((issue, idx) => (
                  <div key={idx} className="bg-slate-900 border border-slate-800 rounded-lg p-5 flex items-start justify-between hover:border-slate-700 transition-colors">
                    <div className="flex gap-4">
                      <div className={`mt-1 p-2 rounded-lg ${
                        issue.type === 'critical' ? 'bg-red-500/10 text-red-500' : 
                        issue.type === 'warning' ? 'bg-amber-500/10 text-amber-500' : 'bg-blue-500/10 text-blue-500'
                      }`}>
                        {issue.type === 'critical' ? <Icons.AlertCircle className="w-5 h-5" /> : <Icons.AlertTriangle className="w-5 h-5" />}
                      </div>
                      <div>
                        <h4 className="font-semibold text-white text-base">{issue.title}</h4>
                        <p className="text-sm text-slate-400 mt-1">Affects {issue.count} pages</p>
                      </div>
                    </div>
                    <button 
                      onClick={() => setActiveTab('issues')}
                      className="px-4 py-2 bg-slate-800 hover:bg-slate-700 text-slate-300 text-sm rounded-lg transition-colors"
                    >
                      Fix Issue
                    </button>
                  </div>
                ))
              )}
            </div>
          </div>
        )}

        {activeTab === 'issues' && (
          <div className="space-y-4">
            {groupedIssues.map((group, idx) => (
              <div key={idx} className="bg-slate-900 border border-slate-800 rounded-xl overflow-hidden">
                 <div className="p-4 bg-slate-800/50 border-b border-slate-800 flex justify-between items-center cursor-pointer">
                    <div className="flex items-center gap-3">
                      <Badge type={group.type}>{group.type.toUpperCase()}</Badge>
                      <span className="font-semibold text-slate-200">{group.title}</span>
                    </div>
                    <span className="text-slate-500 text-sm">{group.count} URLs</span>
                 </div>
                 <div className="p-4 bg-slate-900/50 max-h-48 overflow-y-auto">
                    <ul className="space-y-2">
                      {group.urls.map((u, i) => (
                        <li key={i} className="text-sm text-slate-400 font-mono hover:text-indigo-400 cursor-pointer flex items-center gap-2">
                          <Icons.ChevronRight className="w-3 h-3" />
                          {u}
                        </li>
                      ))}
                    </ul>
                 </div>
              </div>
            ))}
          </div>
        )}

        {activeTab === 'pages' && (
          <div className="bg-slate-900 border border-slate-800 rounded-xl overflow-hidden">
            <div className="overflow-x-auto">
              <table className="w-full text-left text-sm">
                <thead>
                  <tr className="border-b border-slate-800 bg-slate-800/50 text-slate-400">
                    <th className="p-4 font-semibold">URL</th>
                    <th className="p-4 font-semibold">Status</th>
                    <th className="p-4 font-semibold">TTFB</th>
                    <th className="p-4 font-semibold">Issues</th>
                  </tr>
                </thead>
                <tbody className="divide-y divide-slate-800">
                  {results.map((page, idx) => (
                    <tr key={idx} className="hover:bg-slate-800/50 transition-colors">
                      <td className="p-4 font-mono text-slate-300 truncate max-w-xs" title={page.url}>{page.url}</td>
                      <td className="p-4">
                        <span className={`px-2 py-1 rounded text-xs font-bold ${
                          page.statusCode >= 400 ? 'bg-red-500/20 text-red-400' : 'bg-emerald-500/20 text-emerald-400'
                        }`}>
                          {page.statusCode}
                        </span>
                      </td>
                      <td className="p-4">
                         <span className={page.ttfb > 1.0 ? 'text-amber-400' : 'text-slate-400'}>{page.ttfb.toFixed(2)}s</span>
                      </td>
                      <td className="p-4">
                        {page.issues.length > 0 ? (
                          <div className="flex gap-1">
                             {page.issues.slice(0,3).map((iss, i) => (
                               <div key={i} className={`w-2 h-2 rounded-full ${
                                 iss.type === 'critical' ? 'bg-red-500' : 'bg-amber-500'
                               }`} title={iss.message}></div>
                             ))}
                             {page.issues.length > 3 && <span className="text-xs text-slate-500">+{page.issues.length - 3}</span>}
                          </div>
                        ) : (
                          <span className="text-emerald-500 text-xs">Clean</span>
                        )}
                      </td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          </div>
        )}
      </div>
    </div>
  );
};

// --- RENDER ---
const container = document.getElementById('root');
if (container) {
  const root = createRoot(container);
  root.render(<App />);
}