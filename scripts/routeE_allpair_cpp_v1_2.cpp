#include <bits/stdc++.h>
using namespace std;
using i64 = long long;
using i128 = __int128_t;

static const int SEL[32] = {
    0,0,0,4,4,4,1,1,
    1,1,3,4,4,4,3,0,
    0,0,0,3,2,4,2,0,
    1,1,1,0,2,0,0,0
};
static const int PI_[10]={0,0,0,0,1,1,1,2,2,3};
static const int PJ_[10]={1,2,3,4,2,3,4,3,4,4};
int PIND[5][5];

string i128_to_string(i128 x){
    if(x==0) return "0";
    bool neg=x<0; if(neg) x=-x;
    string s; while(x){ int d=(int)(x%10); s.push_back('0'+d); x/=10; }
    if(neg) s.push_back('-'); reverse(s.begin(),s.end()); return s;
}

i64 egcd(i64 a,i64 b,i64 &x,i64 &y){
    if(b==0){ x=1; y=0; return a>=0?a:-a; }
    i64 x1,y1; i64 g=egcd(b,a%b,x1,y1); x=y1; y=x1-(a/b)*y1; return g;
}
i64 inv_mod(i64 a,i64 m){
    i64 x,y; i64 g=egcd(a,m,x,y); (void)g;
    x%=m; if(x<0) x+=m; return x;
}
int selector_arr(const array<i64,5>& w){
    int idx=0;
    if(w[1]==0) idx|=1;
    if(w[2]==0) idx|=2;
    if(w[3]==0) idx|=4;
    if(w[4]==0) idx|=8;
    if(w[0]==0) idx|=16;
    return SEL[idx];
}
array<i64,5> inc_for_selector(i64 m,i64 x,i64 z,int s){
    array<i64,5> inc = {x%m, (m-1-x-z)%m, 0, z%m, 0};
    for(auto &v: inc){ v%=m; if(v<0)v+=m; }
    inc[s]=(inc[s]+1)%m;
    return inc;
}
i64 next_zero_event(const array<i64,5>& w,i64 m,const array<i64,5>& inc){
    const i64 INF = LLONG_MAX/4;
    i64 best=INF;
    for(int j=0;j<5;j++){
        i64 ww=w[j]%m; if(ww<0)ww+=m;
        i64 ii=inc[j]%m; if(ii<0)ii+=m;
        if(ii==0) continue;
        i64 t;
        if(ww==0) t=1;
        else{
            i64 g=std::gcd(ii,m);
            if(ww%g!=0) continue;
            i64 M=m/g;
            i64 a=(ii/g)%M;
            i64 b=((-ww/g)%M+M)%M;
            t=(i128)b*inv_mod(a,M)%M;
            if(t==0) t=M;
        }
        if(t<best) best=t;
    }
    if(best==INF) return m;
    return best;
}
struct Jump { array<i64,5> nw; i64 step; int sel; };
Jump step_jump(array<i64,5> w,i64 m,i64 x,i64 z){
    int s=selector_arr(w);
    auto inc=inc_for_selector(m,x,z,s);
    i64 t=next_zero_event(w,m,inc);
    for(int j=0;j<5;j++) w[j]=(w[j]+(i128)t*inc[j])%m;
    return {w,t,s};
}
array<i64,5> idx_to_w(int idx,i64 m){
    array<i64,5> w={0,0,0,0,0};
    if(idx==0) return w;
    int t=idx-1; int p=t/(m-1); int a=t%(m-1)+1;
    int i=PI_[p], j=PJ_[p];
    w[i]=a; w[j]=(m-a)%m;
    return w;
}
int pair_idx_from_w(const array<i64,5>& w,i64 m){
    vector<int> nz;
    for(int i=0;i<5;i++){ i64 v=w[i]%m; if(v<0)v+=m; if(v!=0) nz.push_back(i); }
    if(nz.empty()) return 0;
    if(nz.size()==2){
        int a=nz[0], b=nz[1];
        if(((w[a]+w[b])%m+m)%m==0){
            int i=a,j=b; if(i>j) swap(i,j);
            int p=PIND[i][j];
            i64 aa=w[i]%m; if(aa<0)aa+=m;
            return 1+p*(m-1)+(int)(aa-1);
        }
    }
    return -1;
}
string node_label(int idx,i64 m){
    if(idx<0) return "null";
    if(idx==0) return "Z";
    int t=idx-1; int p=t/(m-1); int a=t%(m-1)+1;
    return "("+to_string(PI_[p])+","+to_string(PJ_[p])+","+to_string(a)+")";
}
string skeleton_label(int idx,i64 m){
    static vector<string> labels={"Z","01","02","03","04","12","13","14","23","24","34"};
    if(idx<0) return "null";
    if(idx==0) return "Z";
    int p=(idx-1)/(m-1);
    return labels[1+p];
}
int node_a_value(int idx,i64 m){
    if(idx<=0) return 0;
    return (idx-1)%(m-1)+1;
}
struct FirstRet { int dst; i128 time; int events; };
FirstRet allpair_first_return(i64 m,i64 x,i64 z,int idx,int cap_events,i128 max_time){
    array<i64,5> w=idx_to_w(idx,m);
    i128 total=0; int events=0;
    while(events<cap_events){
        Jump jp=step_jump(w,m,x,z);
        if(total+jp.step>max_time) return {-2,total+jp.step,events};
        w=jp.nw; total+=jp.step; events++;
        int j=pair_idx_from_w(w,m);
        if(j>=0) return {j,total,events};
    }
    return {-1,total,events};
}
struct ScanResult{
    bool ok=false; int fail_idx=-1; int fail_status=0; i128 total=0; int max_events=0; i128 max_return_time=0; vector<int> nxt; vector<i128> times; vector<int> events;
};
ScanResult allpair_scan(i64 m,i64 x,i64 z,int cap_events,i128 max_time,bool keep_arrays){
    int N=1+10*(m-1);
    ScanResult R; R.ok=true; if(keep_arrays){ R.nxt.resize(N); R.times.resize(N); R.events.resize(N); }
    for(int idx=0; idx<N; idx++){
        auto fr=allpair_first_return(m,x,z,idx,cap_events,max_time);
        if(fr.dst<0){ R.ok=false; R.fail_idx=idx; R.fail_status=fr.dst; return R; }
        R.total += fr.time;
        R.max_events=max(R.max_events, fr.events);
        if(fr.time>R.max_return_time) R.max_return_time=fr.time;
        if(keep_arrays){ R.nxt[idx]=fr.dst; R.times[idx]=fr.time; R.events[idx]=fr.events; }
    }
    return R;
}
vector<int> cycle_lengths(const vector<int>& nxt){
    int N=nxt.size(); vector<char> seen(N,false); vector<int> lens;
    for(int i=0;i<N;i++) if(!seen[i]){
        int cur=i,cnt=0;
        while(cur>=0 && cur<N && !seen[cur]){ seen[cur]=true; cnt++; cur=nxt[cur]; }
        lens.push_back(cnt);
    }
    sort(lens.rbegin(),lens.rend()); return lens;
}
bool single_cycle(const vector<int>& nxt){ auto L=cycle_lengths(nxt); return L.size()==1 && L[0]==(int)nxt.size(); }

bool count_admissible(i64 m,i64 x,i64 z){ return x>0 && z>0 && x+z<=m-1; }
bool unit_pair(i64 m,i64 x,i64 z){ return count_admissible(m,x,z) && std::gcd(x,m)==1 && std::gcd(z,m)==1; }
vector<pair<int,int>> candidate_pairs(int m,string suite,int limit){
    vector<pair<int,int>> out; set<pair<int,int>> seen;
    auto add=[&](int x,int z){ if(x>=1&&z>=1&&x<m&&z<m&&x+z<=m-1 && !seen.count({x,z})){ seen.insert({x,z}); out.push_back({x,z}); } };
    int small = min(m-1, suite=="wide"?35:18);
    for(int c=1;c<=small;c++) add(c,c);
    for(int x=1;x<=small;x++) for(int z=1;z<=small;z++) add(x,z);
    vector<int> centers;
    for(int denom: {16,14,12,10,8,6,5,4,3,2}) for(int off=-5; off<=5; off++){
        centers.push_back(m/denom+off); centers.push_back((m-2)/denom+off); centers.push_back((m+2)/denom+off);
    }
    for(int c: centers) add(c,c);
    for(int x=1;x<=small;x++) for(int cc: {2,4,6,8,10,12,14,16,18,20,24,28,32}){
        if((m-cc)%2==0) add(x,(m-cc)/2);
        if((m-cc)%3==0) add(x,(m-cc)/3);
    }
    for(int val: {(m-2)/12,(m-2)/6,(m+4)/6,(m-2)/4,(m-6)/2}) for(int dx=-4; dx<=4; dx++) add(val+dx,val+dx);
    if(m%96==38){ int n=(m-38)/96; add(8*n+3,8*n+3); add(20*n+3,20*n+3); }
    if(m%96==86){ int n=(m-86)/96; add(8*n+7,3); add(8*n+7,8*n+7); }
    if(limit>0 && (int)out.size()>limit) out.resize(limit);
    return out;
}

void init(){ for(int i=0;i<5;i++)for(int j=0;j<5;j++)PIND[i][j]=-1; for(int p=0;p<10;p++){ PIND[PI_[p]][PJ_[p]]=p; PIND[PJ_[p]][PI_[p]]=p; } }

void cmd_check(int argc,char**argv){
    if(argc<6){ cerr<<"usage: check m x z cap_events\n"; exit(2); }
    i64 m=stoll(argv[2]), x=stoll(argv[3]), z=stoll(argv[4]); int cap=stoi(argv[5]);
    auto R=allpair_scan(m,x,z,cap,(i128)LLONG_MAX*LLONG_MAX,true);
    bool sumok=R.total==(i128)m*m*m*m; vector<int> lens=R.ok?cycle_lengths(R.nxt):vector<int>{};
    cout<<"{\n  \"schema\":\"routeE_allpair_cpp_check_v1_2\",\n";
    cout<<"  \"m\":"<<m<<", \"x\":"<<x<<", \"z\":"<<z<<",\n";
    cout<<"  \"count_admissible\":"<<(count_admissible(m,x,z)?"true":"false")<<", \"unit_pair\":"<<(unit_pair(m,x,z)?"true":"false")<<",\n";
    cout<<"  \"ok_returns\":"<<(R.ok?"true":"false")<<", \"time_sum\":"<<i128_to_string(R.total)<<", \"m4\":"<<i128_to_string((i128)m*m*m*m)<<", \"sum_ok\":"<<(sumok?"true":"false")<<",\n";
    cout<<"  \"single_cycle\":"<<((R.ok && lens.size()==1 && lens[0]==(int)R.nxt.size())?"true":"false")<<", \"cycle_lengths_top\":[";
    for(size_t i=0;i<min<size_t>(lens.size(),8);i++){ if(i)cout<<","; cout<<lens[i]; } cout<<"],\n";
    cout<<"  \"max_events\":"<<R.max_events<<", \"max_return_time\":"<<i128_to_string(R.max_return_time)<<", \"fail_idx\":"<<R.fail_idx<<", \"fail_label\":\""<<node_label(R.fail_idx,m)<<"\"\n}\n";
}
void cmd_search_range(int argc,char**argv){
    if(argc<8){ cerr<<"usage: search-range m_min m_max step suite limit cap_events [out]\n"; exit(2); }
    int mmin=stoi(argv[2]), mmax=stoi(argv[3]), step=stoi(argv[4]); string suite=argv[5]; int limit=stoi(argv[6]); int cap=stoi(argv[7]); string outpath=argc>8?argv[8]:"";
    ostringstream os; os<<"{\n  \"schema\":\"routeE_allpair_cpp_range_search_v1_2\",\n  \"rows\":[\n";
    bool firstrow=true;
    for(int m=mmin;m<=mmax;m+=step){
        auto pairs=candidate_pairs(m,suite,limit); vector<tuple<int,int,int,bool,int,i128>> hits; int checked=0;
        for(int idx=0; idx<(int)pairs.size(); idx++){
            auto [x,z]=pairs[idx]; checked++;
            auto R=allpair_scan(m,x,z,cap,(i128)m*m*m*m+1,true);
            if(R.ok && R.total==(i128)m*m*m*m){
                auto lens=cycle_lengths(R.nxt);
                if(lens.size()==1 && lens[0]==(int)R.nxt.size()){
                    hits.push_back({x,z,idx,unit_pair(m,x,z),R.max_events,R.max_return_time});
                    if(hits.size()>=3) break;
                }
            }
        }
        if(!firstrow) os<<",\n"; firstrow=false;
        os<<"    {\"m\":"<<m<<",\"candidate_count\":"<<pairs.size()<<",\"checked\":"<<checked<<",\"hits\":[";
        for(size_t h=0; h<hits.size(); h++){
            if(h) os<<",";
            auto [x,z,idx,u,me,mt]=hits[h];
            os<<"{\"x\":"<<x<<",\"z\":"<<z<<",\"candidate_index\":"<<idx<<",\"unit_pair\":"<<(u?"true":"false")<<",\"max_events\":"<<me<<",\"max_return_time\":"<<i128_to_string(mt)<<"}";
        }
        os<<"]}";
    }
    os<<"\n  ]\n}\n";
    string res=os.str(); if(!outpath.empty()){ ofstream f(outpath); f<<res; } cout<<res;
}
void cmd_symmetric(int argc,char**argv){
    if(argc<8){ cerr<<"usage: symmetric m_min m_max step cmax cap_events out\n"; exit(2); }
    int mmin=stoi(argv[2]), mmax=stoi(argv[3]), step=stoi(argv[4]), cmax=stoi(argv[5]), cap=stoi(argv[6]); string outpath=argv[7];
    ostringstream os; os<<"{\n \"schema\":\"routeE_symmetric_cpp_dashboard_v1_2\",\n \"rows\":[\n"; bool fr=true;
    for(int m=mmin;m<=mmax;m+=step){
        vector<tuple<int,int,i128>> hits;
        for(int c=1;c<=min(cmax,(m-1)/2);c++){
            auto R=allpair_scan(m,c,c,cap,(i128)m*m*m*m+1,true);
            if(R.ok && R.total==(i128)m*m*m*m){ auto lens=cycle_lengths(R.nxt); if(lens.size()==1 && lens[0]==(int)R.nxt.size()){ hits.push_back({c,R.max_events,R.max_return_time}); if(hits.size()>=5) break; } }
        }
        if(!fr) os<<",\n"; fr=false; os<<"  {\"m\":"<<m<<",\"hits\":[";
        for(size_t i=0;i<hits.size();i++){ if(i)os<<","; auto [c,e,t]=hits[i]; os<<"{\"c\":"<<c<<",\"max_events\":"<<e<<",\"max_return_time\":"<<i128_to_string(t)<<"}"; }
        os<<"]}";
    }
    os<<"\n ]\n}\n"; string res=os.str(); ofstream f(outpath); f<<res; cout<<res;
}
void cmd_enum_small(int argc,char**argv){
    if(argc<7){ cerr<<"usage: enum-small m_min m_max step cap_events out\n"; exit(2); }
    int mmin=stoi(argv[2]),mmax=stoi(argv[3]),step=stoi(argv[4]),cap=stoi(argv[5]); string outpath=argv[6];
    ostringstream os; os<<"{\n \"schema\":\"routeE_exhaustive_cpp_v1_2\",\n \"rows\":[\n"; bool fr=true;
    for(int m=mmin;m<=mmax;m+=step){
        int total_pairs=0, ok_pairs=0, sum_pairs=0, single_pairs=0; vector<pair<int,int>> singles;
        for(int x=1;x<m;x++)for(int z=1;z<m;z++)if(x+z<=m-1){ total_pairs++; auto R=allpair_scan(m,x,z,cap,(i128)m*m*m*m+1,true); if(R.ok){ ok_pairs++; if(R.total==(i128)m*m*m*m) sum_pairs++; auto lens=cycle_lengths(R.nxt); if(lens.size()==1&&lens[0]==(int)R.nxt.size()){ single_pairs++; if(singles.size()<8) singles.push_back({x,z}); } } }
        if(!fr) os<<",\n"; fr=false; os<<"  {\"m\":"<<m<<",\"count_pairs\":"<<total_pairs<<",\"ok_returns\":"<<ok_pairs<<",\"sum_ok\":"<<sum_pairs<<",\"single_cycle\":"<<single_pairs<<",\"first_singles\":[";
        for(size_t i=0;i<singles.size();i++){ if(i)os<<","; os<<"["<<singles[i].first<<","<<singles[i].second<<"]"; } os<<"]}";
    }
    os<<"\n ]\n}\n"; string res=os.str(); ofstream f(outpath); f<<res; cout<<res;
}
void cmd_dump_csv(int argc,char**argv){
    if(argc<7){ cerr<<"usage: dump-csv m x z cap_events out.csv\n"; exit(2); }
    i64 m=stoll(argv[2]), x=stoll(argv[3]), z=stoll(argv[4]);
    int cap=stoi(argv[5]);
    string outpath=argv[6];
    int N=1+10*(m-1);
    ofstream f(outpath);
    f<<"idx,src_label,src_a,dst_idx,dst_label,dst_a,time,events\n";
    i128 total=0; int max_events=0;
    for(int idx=0; idx<N; idx++){
        auto fr=allpair_first_return(m,x,z,idx,cap,(i128)LLONG_MAX*LLONG_MAX);
        if(fr.dst<0){
            cerr<<"fail idx "<<idx<<" status "<<fr.dst<<"\n";
            exit(1);
        }
        total += fr.time;
        max_events=max(max_events, fr.events);
        f<<idx<<","<<skeleton_label(idx,m)<<","<<node_a_value(idx,m)<<","
         <<fr.dst<<","<<skeleton_label(fr.dst,m)<<","<<node_a_value(fr.dst,m)<<","
         <<i128_to_string(fr.time)<<","<<fr.events<<"\n";
    }
    cerr<<"wrote "<<outpath<<" N="<<N<<" total="<<i128_to_string(total)
        <<" m4="<<i128_to_string((i128)m*m*m*m)<<" max_events="<<max_events<<"\n";
}
int main(int argc,char**argv){
    ios::sync_with_stdio(false); cin.tie(nullptr); init();
    if(argc<2){ cerr<<"commands: check, search-range, symmetric, enum-small, dump-csv\n"; return 2; }
    string cmd=argv[1];
    if(cmd=="check") cmd_check(argc,argv);
    else if(cmd=="search-range") cmd_search_range(argc,argv);
    else if(cmd=="symmetric") cmd_symmetric(argc,argv);
    else if(cmd=="enum-small") cmd_enum_small(argc,argv);
    else if(cmd=="dump-csv") cmd_dump_csv(argc,argv);
    else { cerr<<"unknown command\n"; return 2; }
}
