#include<bits/stdc++.h>

using i8=char;		using u8=unsigned char;
using i16=short;	using u16=unsigned short;
using i32=int;		using u32=unsigned int;
using i64=long long;using u64=unsigned long long;
using i128=__int128;using u128=unsigned __int128;
using f32=float; 	using f64=double;				using f128=long double;

template<typename T> inline void read(T &x){
	char ch=getchar(),f=0;
	x=0;
	while(ch<'0'||ch>'9')f|=(ch=='-'),ch=getchar();
	while(ch>='0'&&ch<='9')(x=x*10+(ch-'0')),ch=getchar();
	x=(f?-x:x);
}
template<typename T,typename ...Ts> void read(T &x,Ts &...xs){read(x); read(xs...); }
char fostk[50]; u8 cntfostk;
template<typename T> inline void write(T x){
	if(x<0)putchar('-'),x=-x;
	while(x>9)fostk[++cntfostk]='0'+x%10,x/=10;
	fostk[++cntfostk]=x+'0';
	while(cntfostk)putchar(fostk[cntfostk--]);
}
template<typename T> void writesp(T x){write(x); putchar(' '); }
template<typename T> void writeln(T x){write(x); putchar('\n'); }
template<typename T> void writelns(T x){writeln(x); }
template<typename T,typename ...Ts> void write(T x,Ts ...xs){writesp(x); write(xs...); }
template<typename T,typename ...Ts> void writeln(T x,Ts ...xs){write(x,xs...); putchar('\n'); }
template<typename T,typename ...Ts> void writelns(T x,Ts ...xs){writeln(x); writelns(xs...); }
struct Edge{
	int to,next;
}e[1000005];
i32 head[500005],cntedge;
void addedge(i32 u,i32 v){
	e[++cntedge].to=v;
	e[cntedge].next=head[u];
	head[u]=cntedge;
}
namespace Trie{
	struct Node{
		i32 s[2],cnt,xr;
	}nod[10100008];
	i32 st[1000005];
	i32 cnt;
	i32 getnode(){
		int re=++cnt;
		nod[re].s[0]=nod[re].s[1]=0;
		nod[re].cnt=0;
		nod[re].xr=0;
		return re;
	}
	void ins(i32 x,i32 rt,i32 dep,i32 idx){
		if(dep>20)return;
		if(!nod[rt].s[(x>>dep)&1])nod[rt].s[(x>>dep)&1]=getnode();
		ins(x,nod[rt].s[(x>>dep)&1],dep+1,(x>>dep)&1);
		i32 s0=nod[rt].s[0],s1=nod[rt].s[1];
		nod[rt].cnt++;
		i32 ct=((nod[rt].cnt&1)&idx);
		nod[rt].xr=nod[s0].xr^nod[s1].xr;
		// fprintf(stderr,"Trie::ins dep:%d idx:%d nod[rt:%d].xr:%d nod[rt:%d].cnt:%d ct:%d (nod[s0:%d].xr:%d^nod[s1:%d].xr:%d):%d\n",
			// dep,idx,rt,nod[rt].xr,rt,nod[rt].cnt,ct,s0,nod[s0].xr,s1,nod[s1].xr,(nod[s0].xr^nod[s1].xr));
		if(dep!=0)nod[rt].xr=((nod[rt].xr<<1)|ct);
		// fprintf(stderr,"Trie::ins nod[rt:%d].xr:%d\n",rt,nod[rt].xr);
		return ;
	}
	void insert(i32 x,i32 p){
		st[p]=(st[p]?st[p]:getnode());
		// fprintf(stderr,"Trie::insert x:%d st[p:%d]:%d\n",x,p,st[p]);
		ins(x,st[p],0,0);
		return ;
	}	
	i32 qry(i32 p){
		st[p]=(st[p]?st[p]:getnode());
		// fprintf(stderr,"Trie::qry nod[st[p:%d]:%d].xr:%d\n",p,st[p],nod[st[p]].xr);
		return nod[st[p]].xr;
	}
	void dfs(i32 x){
		std::swap(nod[x].s[0],nod[x].s[1]);
		// fprintf(stderr,"Trie::dfs nod[x:%d].s[0]:%d nod[x:%d].s[1]:%d\n",x,nod[x].s[0],x,nod[x].s[1]);
		if(nod[x].s[0]){
			// fprintf(stderr,"Trie::dfsin nod[x:%d].s[0]:%d\n",x,nod[x].s[0]);
			dfs(nod[x].s[0]);
		}
		i32 s0=nod[x].s[0],s1=nod[x].s[1];
		// fprintf(stderr,"Trie::dfs nod[s0:%d].xr:%d\t",s0,nod[s0].xr);
		i32 ss0=nod[s0].s[0],ss1=nod[s0].s[1];
		nod[s0].xr=((nod[ss0].xr^nod[ss1].xr)<<1);
		// fprintf(stderr,"Trie::dfs nod[s0:%d].xr:%d\nTrie::dfs nod[s1:%d].xr:%d nod[s1:%d].cnt:%d\t"
			// ,s0,nod[s0].xr,s1,nod[s1].xr,s1,nod[s1].cnt);
		ss0=nod[s1].s[0],ss1=nod[s1].s[1];
		nod[s1].xr=(((nod[ss0].xr^nod[ss1].xr)<<1)|(nod[s1].cnt&1));	
		// fprintf(stderr,"Trie::dfs nod[s1:%d].xr:%d\n",s1,nod[s1].xr);
		return;
	}
	void add1(i32 p){
		st[p]=(st[p]?st[p]:getnode());
		// fprintf(stderr,"Trie::add1 st[p:%d]:%d\n",p,st[p]);
		dfs(st[p]);
		i32 s0=nod[st[p]].s[0],s1=nod[st[p]].s[1];
		nod[st[p]].xr=nod[s0].xr^nod[s1].xr;
		// fprintf(stderr,"Trie::add1 nod[st[p:%d]:%d].xr:%d\n",p,st[p],nod[st[p]].xr);
		return;
	}
}
struct Node{
	i32 tag,fa,v;
}nod[1000005];
void add(i32 x){
	nod[x].tag++;
	i32 fa=nod[x].fa;
	if(fa){
		nod[fa].v++;
		if(nod[fa].fa){
			i32 v=nod[fa].v+nod[nod[fa].fa].tag-1;
			i32 pa=nod[fa].fa;
			Trie::insert(v,pa);
			v++;
			Trie::insert(v,pa);	
		}
	}
	Trie::add1(x);
	return;
}
void minus(i32 x,i32 v){
	if(x!=1){
		i32 fa=nod[x].fa;
		// fprintf(stderr,"::minus (nod[x:%d].v:%d+nod[fa:%d].tag:%d):%d\n",
			// x,nod[x].v,fa,nod[fa].tag,(nod[x].v+nod[fa].tag));
		Trie::insert(nod[x].v+nod[fa].tag,fa);
		// fprintf(stderr,"::minus (nod[x:%d].v:%d+nod[fa:%d].tag:%d-v:%d):%d\n",
			// x,nod[x].v,fa,nod[fa].tag,v,(nod[x].v+nod[fa].tag-v));
		Trie::insert(nod[x].v+nod[fa].tag-v,fa);
	}
	// fprintf(stderr,"::minus1 (nod[x:%d].v:%d-v:%d):%d\n",x,nod[x].v,v,nod[x].v-v);
	nod[x].v-=v;
	// fprintf(stderr,"::minus2 nod[x:%d].v:%d\n",x,nod[x].v);
	return;
}
i32 qry(i32 x){
	int fa=nod[x].fa;
	// fprintf(stderr,"::qry Trie::qry(x:%d):%d^(nod[nod[fa:%d].fa:%d].tag:%d+nod[fa:%d].v:%d):%d\n",
		// x,Trie::qry(x),x,nod[fa].fa,nod[nod[fa].fa].tag,fa,nod[fa].v,Trie::qry(x)^(nod[nod[fa].fa].tag+nod[fa].v));
	return Trie::qry(x)^(nod[nod[fa].fa].tag+nod[fa].v);
}
void dfs(i32 x,i32 fa){
	nod[x].fa=fa;
	for(int i=head[x];i;i=e[i].next){
		if(e[i].to==fa)continue;
		dfs(e[i].to,x);
	}
	return;
}
int n,m;
i32 main(){
#ifdef LOCAL
	freopen("test.in","r",stdin);
	freopen("test.out","w",stdout);
	freopen("test.err","w",stderr);
#endif
	read(n,m);
	for(i32 i=1;i<n;i++){
		i32 u,v;
		read(u,v);
		addedge(u,v);
		addedge(v,u);
	}
	for(i32 i=1;i<=n;i++){
		read(nod[i].v);
	}	
	dfs(1,0);
	for(i32 i=2;i<=n;i++){
		Trie::insert(nod[i].v,nod[i].fa);
	}
	for(i32 i=1;i<=m;i++){
		i32 opt,x;
		read(opt,x);
		if(opt==1){
			add(x);
		}else if(opt==2){
			i32 v;
			read(v);
			minus(x,v);
		}else if(opt==3){
			writeln(qry(x));
		}
	}
	return 0;
}