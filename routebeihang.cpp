#include "route.h"
#include "lib_record.h"
#include<cstdio>
#include<cstring>
#include<algorithm>
#include<vector>
#include<queue>
#include<deque>
#include<cmath>
#include<ctime>
#include<stack>
#include<iostream>
using namespace std;
#define N 2000
#define M 40000
#define INF 1000000
struct edge
{	int id,u,v,w;
	edge(int id=0,int u=0,int v=0,int w=0):id(id),u(u),v(v),w(w) {}
};
int graph1[N+10][N+10];
int cost1[N+10][N+10];
int graph2[N+10][N+10];
int cost2[N+10][N+10];
int graph[N+10][N+10];
int cost[N+10][N+10];
int uses[N+10][N+10];
vector<int> Vset;
int ed_id[M+10];
edge ed[M+10];
bool inV[N+10];
int last[N+10];
int pre[M+10];
int e[M+10];
int n,m,src,dest;
//Global variables for the original graph

int label[N+10];


int counter;
deque<vector<int> > former_ans;
vector<int> r_res1,r_res2;
int coincide,r_cost;

vector<int> ansset;
vector<int> anssets;
int my_ans=110000000;
int my_repeat=1100000;
int my_size;
int my_pp[N+10];
int my_flag;
int val[N+10];
struct my_node
{
	int x,y;
};
int cmp(my_node a,my_node b)
{
	return a.x>b.x;
}
int cal(int x)
{
	if (n<100) return max(133-x,1);
	else return max(49-x,1);
}

int dfs_size;
int dfs_pp[N+10];
int dfs_bad;
int dfs_hui[N+10];
int dfs_dfn[N+10];
int dfs_order[N+10];
int dfs_count;
int valuesdfs(int x)
{
	dfs_count++;
	dfs_order[x]=dfs_count;
	dfs_pp[x]=1;
	
	int haha=0;
	if (inV[x]) dfs_size++;
	for (int i=last[x];i!=0;i=pre[i])
	{
		if (dfs_pp[e[i]]) dfs_dfn[x]=min(dfs_dfn[x],dfs_order[e[i]]);
		if (dfs_pp[e[i]]) continue;
		haha+=valuesdfs(e[i]);
		if (haha>2) dfs_bad=1;
		if (haha) return 1;
		dfs_dfn[x]=min(dfs_dfn[x],dfs_dfn[e[i]]);
	}
	if (haha>2) dfs_bad=1;
	if (dfs_dfn[x]>=dfs_order[x]&&inV[x]&&x!=dest) return 1;
	if (haha) return 1;
	else return 0;
}
int value(int x,int edgecost,int depth)
{	
	if (depth>20)
	{
		dfs_count=0;
		dfs_size=0;
		dfs_bad=0;
		for (int i=1;i<=n;i++)
			dfs_pp[i]=my_pp[i],dfs_dfn[i]=1100000;
		valuesdfs(x);
		if (dfs_bad||dfs_size<my_size) return 0;
	}
	int res=(100-edgecost)*10;
	if (inV[x]) res+=3001;
	for (int i=last[x];i!=0;i=pre[i])
	{
		if (!my_pp[e[i]]) if (inV[e[i]]) res+=807;
		else res+=53;
	}
	return res;
}	
int values(int x,int edgecost,int depth)
{
	if (depth>20)
	{
		dfs_count=0;
		dfs_size=0;
		dfs_bad=0;
		for (int i=1;i<=n;i++)
			dfs_pp[i]=my_pp[i],dfs_dfn[i]=1100000;
		valuesdfs(x);
		if (dfs_bad||dfs_size<my_size)
		{
			 val[x]-=10;
		 	return 0;
		}
	}
	int res=(100-edgecost)*10+val[x];
	if (inV[x]) res+=3001;
	for (int i=last[x];i!=0;i=pre[i])
	{
		if (!my_pp[e[i]]) if (inV[e[i]]) res+=807;
		else res+=53;
	}
	return res;
}
int que[1100000];
int way[N+10];
int d[N+10];
int dr[N+10];
int dd[N+10];
int head,tail;
int ways[N+10];
int mod=1100000;
int formerlimit;
int laterlimit;
my_node glob_a[N+10][N+10];
void my_dfs(int x,int depth,int sum)
{
	counter++;
	if (sum+dd[x]>my_ans) return;
	if (counter>=60000000/n/4*10) return;
	if (inV[x]) my_size--;
	my_pp[x]=1;
	if (my_size-inV[dest]==0)
	{
		if (x==dest)
		{
			if (sum<my_ans)
			{
				ansset=anssets;
				if (former_ans.size()>10)
					former_ans.pop_back();
				former_ans.push_front(ansset);
				my_ans=sum;
			}
			my_pp[x]=0;
			if (inV[x]) my_size++;
			return;
		}
		head=0,tail=1;
		que[1]=x;
		for (int i=1;i<=n;i++)
			d[i]=11000000;
		d[x]=sum;
		do
		{
			head=(head+1)%mod;
			int now=que[head];
			for (int i=last[now];i!=0;i=pre[i])
			{
				if (my_pp[e[i]]) continue;
				if (d[now]+cost[now][e[i]]<d[e[i]])
				{
					d[e[i]]=d[now]+cost[now][e[i]];
					way[e[i]]=now;
					if (!my_pp[e[i]])
					{
						tail=(tail+1)%mod;
						que[tail]=e[i];
						my_pp[e[i]]=1;
					}
				}
			}
			my_pp[now]=0;
		}while (head!=tail);
		if (inV[x]) my_size++;
		if (d[dest]>=my_ans) return;
		int nway=1;
		ways[1]=dest;
		way[x]=0;
		int pos=dest;
		while (way[pos]!=0)
		{
			nway++;
			ways[nway]=way[pos];
			pos=way[pos];
		}
		for (int i=nway;i>1;i--)
			anssets.push_back(graph[ways[i]][ways[i-1]]);
		my_ans=d[dest];
		ansset=anssets;
		if (former_ans.size()>10)
			former_ans.pop_back();
		former_ans.push_front(ansset);
		for (int i=nway;i>1;i--)
			anssets.pop_back();
		return;
	}
	my_node* a=glob_a[depth];
	int num=0;
	for (int i=last[x];i!=0;i=pre[i])
	{
		if (my_pp[e[i]]) continue;
		num++;
		a[num].x=value(e[i],cost[x][e[i]],depth);
		if (a[num].x<=0)
		{
			num--;
			continue;
		}
		a[num].y=e[i];
	}
	sort(a+1,a+1+num,cmp);
	int l=min(cal(depth),num);
	for (int i=1;i<=l;i++)
	{
		anssets.push_back(graph[x][a[i].y]);
		my_dfs(a[i].y,depth+1,sum+cost[x][a[i].y]);
		anssets.pop_back();
	}
	my_pp[x]=0;
	if (inV[x]) my_size++;
}

void my_dfss(int x,int depth,int sum,int repeat)
{
	counter++;
	if (repeat>my_repeat) return;
	if (repeat+dd[x]>=my_repeat) return;
	if (counter>=9000000/n/4*10) return;
	if (inV[x]) my_size--;
	my_pp[x]=1;
	if (my_size-inV[dest]==0)
	{
		if (x==dest)
		{
			if (sum<my_ans)
			{
				ansset=anssets;
				my_ans=sum;
			}
			my_pp[x]=0;
			if (inV[x]) my_size++;
			return;
		}
		head=0,tail=1;
		que[1]=x;
		for (int i=1;i<=n;i++)
			d[i]=dr[i]=11000000;
		d[x]=sum;
		dr[x]=repeat;
		do
		{
			head=(head+1)%mod;
			int now=que[head];
			for (int i=last[now];i!=0;i=pre[i])
			{
				if (my_pp[e[i]]) continue;
				if ((dr[now]+uses[now][e[i]]<dr[e[i]])
				||(dr[now]+uses[now][e[i]]==dr[e[i]]&&d[now]+cost[now][e[i]]<d[e[i]]))
				{
					d[e[i]]=d[now]+cost[now][e[i]];
					dr[e[i]]=dr[now]+uses[now][e[i]];
					way[e[i]]=now;
					if (!my_pp[e[i]])
					{
						tail=(tail+1)%mod;
						que[tail]=e[i];
						my_pp[e[i]]=1;
					}
				}
			}
			my_pp[now]=0;
		}while (head!=tail);
		if (inV[x]) my_size++;
		if (dr[dest]>my_repeat) return;
		if (dr[dest]==my_repeat&&d[dest]>my_ans) return ;
		int nway=1;
		ways[1]=dest;
		way[x]=0;
		int pos=dest;
		while (way[pos]!=0)
		{
			nway++;
			ways[nway]=way[pos];
			pos=way[pos];
		}
		for (int i=nway;i>1;i--)
			anssets.push_back(graph[ways[i]][ways[i-1]]);
		my_ans=d[dest];
		my_repeat=dr[dest];
		ansset=anssets;
		for (int i=nway;i>1;i--)
			anssets.pop_back();
		return;
	}
	my_node* a=glob_a[depth];
	int num=0;
	for (int i=last[x];i!=0;i=pre[i])
	{
		if (my_pp[e[i]]) continue;
		num++;
		a[num].x=value(e[i],cost[x][e[i]],depth);
		if (a[num].x<=0)
		{
			num--;
			continue;
		}
		a[num].y=e[i];
	}
	sort(a+1,a+1+num,cmp);
	int l=min(cal(depth),num);
	for (int i=1;i<=l;i++)
	{
		anssets.push_back(graph[x][a[i].y]);
		my_dfss(a[i].y,depth+1,sum+cost[x][a[i].y],repeat+uses[x][a[i].y]);
		anssets.pop_back();
	}
	my_pp[x]=0;
	if (inV[x]) my_size++;
}
vector<int> my_work()
{
	memset(my_pp,0,sizeof(my_pp));
	formerlimit=100000/n;
	que[1]=dest;
	head=0;
	tail=1;
	my_pp[dest]=1;
	for (int i=1;i<=n;i++)
		dd[i]=11000000;
	dd[dest]=0;
	do
	{
		head=(head+1)%mod;
		int now=que[head];
		for (int i=1;i<=n;i++)
		    if (graph[i][now]!=0)
		    {
				if (dd[now]+cost[i][now]<dd[i])
				{
					dd[i]=dd[now]+cost[i][now];
					if (!my_pp[i])
					{
						tail=(tail+1)%mod;
						que[tail]=i;
						my_pp[i]=1;
					}
				}
			}
		my_pp[now]=0;
	}while(head!=tail);	
	memset(my_pp,0,sizeof(my_pp));
	my_size=Vset.size();
	ansset.clear();
	anssets.clear();
	my_dfs(src,1,0);
	return ansset;
}
vector<int> my_works()
{
	memset(my_pp,0,sizeof(my_pp));
	que[1]=dest;
	head=0;
	tail=1;
	my_pp[dest]=1;
	for (int i=1;i<=n;i++)
		dd[i]=11000000;
	dd[dest]=0;
	do
	{
		head=(head+1)%mod;
		int now=que[head];
		for (int i=1;i<=n;i++)
		    if (graph[i][now]!=0)
		    {
				if (dd[now]+uses[i][now]<dd[i])
				{
					dd[i]=dd[now]+uses[i][now];
					if (!my_pp[i])
					{
						tail=(tail+1)%mod;
						que[tail]=i;
						my_pp[i]=1;
					}
				}
			}
		my_pp[now]=0;
	}while(head!=tail);	
	memset(my_pp,0,sizeof(my_pp));
	my_size=Vset.size();
	ansset.clear();
	anssets.clear();
	my_dfss(src,1,0,0);
	return ansset;
}
void update(const vector<int>& res1,const vector<int>& res2)
{	static bool rec[40005];
	int i,cc=0,sc=0,u,v;	
	for (int j=0;j<res1.size();++j)
	{	
		
		int u=ed[ed_id[res1[j]]].u,v=ed[ed_id[res1[j]]].v;
		//printf("%d %d\n",u,v);
		sc+=cost1[u][v];
	}
	/*for (i=0;i<res1.size();++i)
	{	u=ed[ed_id[res1[i]]].u,v=ed[ed_id[res1[i]]].v;
		//cost[u][v]/=50;
		uses[u][v]=0;
		sc+=cost[u][v];
	}*/
	if (res2.size()==0)
		return ;
	for (i=0;i<res2.size();++i)
	{	
		u=ed[ed_id[res2[i]]].u,v=ed[ed_id[res2[i]]].v;
		if (graph2[u][v]==0)
		{
			cost[u][v]/=50;
			sc+=cost[u][v];
			uses[u][v]=0;
		}
		else
		{
			graph[u][v]=graph1[u][v];
			sc+=cost[u][v];
			cost[u][v]=cost1[u][v];
		}
	}
	memset(rec,0,sizeof(rec));
	for (i=0;i<res1.size();++i)
		rec[res1[i]]=1;
	for (i=0;i<res2.size();++i)
		cc+=rec[res2[i]];
	if (cc<coincide||(cc==coincide&&sc<r_cost))
	{	coincide=cc,r_cost=sc;
		r_res1=res1;
		r_res2=res2;
	}
}
void search_route(char *topo[MAX_EDGE_NUM], int edge_num, char *demand[MAX_DEMAND_NUM], int demand_num)
{	int i,j,t,u,v,link,ecost;
	vector<int> res;
	char st[20005];
	for (i=0;i<=N;++i)
		for (j=0;j<=N;++j)
			cost1[i][j]=cost2[i][j]=INF;
	coincide=r_cost=INF;
	for (i=0;i<edge_num;++i)
	{	sscanf(topo[i],"%d,%d,%d,%d",&link,&src,&dest,&ecost);
		//swap(src,dest);
		ed[++m]=edge(++link,src,dest,ecost);
		label[src]=label[dest]=1;
	}

	for (i=1;i<=N;++i)
		label[i]+=label[i-1];
	n=label[N];
	//int org[2005]={0};
	for (i=1;i<=m;++i)
	{	//org[label[ed[i].u]]=ed[i].u;
		//org[label[ed[i].v]]=ed[i].v;
		ed[i].u=label[ed[i].u];
		ed[i].v=label[ed[i].v];
	}
	for (i=1;i<=m;++i)
	{
		int u=ed[i].u,v=ed[i].v;
		//du[u]++;
		if (graph1[u][v]==0)
		{
			graph1[u][v]=ed[i].id;
			cost1[u][v]=ed[i].w;
		}
		else if (ed[i].w<cost1[u][v])
		{
			swap(graph1[u][v],graph2[u][v]);
			swap(cost1[u][v],cost2[u][v]);
			graph1[u][v]=ed[i].id;
			cost1[u][v]=ed[i].w;
		}
		else if (ed[i].w<cost2[u][v])
		{
			graph2[u][v]=ed[i].id;
			cost2[u][v]=ed[i].w;
		}
	}
			
	for (int i=1;i<=n;i++)
		for (int j=1;j<=n;j++)
			if (graph1[i][j]&&!graph2[i][j])
			{
				graph2[i][j]=graph1[i][j];
				cost2[i][j]=cost1[i][j];
			}
	for (int i=1;i<=n;i++)
		for (int j=1;j<=n;j++)
			graph[i][j]=graph1[i][j],cost[i][j]=cost1[i][j];
	for (i=1;i<=m;++i)
		if (graph[ed[i].u][ed[i].v]!=ed[i].id)
		{	swap(ed[i],ed[m]);
			--m,--i;
		}
	for (i=1;i<=m;++i)
		if (graph[ed[i].u][ed[i].v]==ed[i].id)
			ed_id[ed[i].id]=i;
 
	for (i=m,m=0;i>0;--i)
		e[++m]=ed[i].v,pre[m]=last[ed[i].u],last[ed[i].u]=m;

	sscanf(demand[0],"%d,%d,%d,%s",&i,&src,&dest,st);
	src=label[src],dest=label[dest];
	//swap(src,dest);
	if (st[0]!='N')
		for (i=0,j=0;st[i]!='\0';++i)
		{	if (st[i+1]=='|'||st[i+1]=='\0')
			{	if (st[i+1]=='|') st[i+1]=' ';
				sscanf(st+j,"%d",&t);
				Vset.push_back(label[t]);
				inV[label[t]]=1;
				j=i+2;
			}
		}
	res=my_work();
	Vset.clear();
	memset(inV,0,sizeof(inV));
	
	sscanf(demand[1],"%d,%d,%d,%s",&i,&src,&dest,st);
	src=label[src],dest=label[dest];
	//swap(src,dest);
	if (st[0]!='N')
		for (i=0,j=0;st[i]!='\0';++i)
		{	if (st[i+1]=='|'||st[i+1]=='\0')
			{	if (st[i+1]=='|') st[i+1]=' ';
				sscanf(st+j,"%d",&t);
				Vset.push_back(label[t]);
				inV[label[t]]=1;
				j=i+2;
			}
		}
	//freopen("rep.txt","w",stderr);
	//int sc=0;
    //laterlimit=min((int)former_ans.size(),formerlimit);
	while (!former_ans.empty())
	{	res=former_ans.front();
		//++sc;
		/*
		for (i=0;i<res.size();++i)
		{	u=ed[ed_id[res[i]]].u,v=ed[ed_id[res[i]]].v;
			//if (sc==1)
			//	fprintf(stderr,"%d|",org[v]);
			cost[u][v]*=50;
			uses[u][v]=1;
		}*/
		//if (sc==1)
		//	fprintf(stderr,"\n");
		memset(my_pp,0,sizeof(my_pp));
		counter=0;
		my_flag=0;
		my_size=Vset.size();
		my_ans=INF;
		ansset.clear();
		anssets.clear();
	
		for (int j=0;j<res.size();++j)
		{	
			
			int u=ed[ed_id[res[j]]].u,v=ed[ed_id[res[j]]].v;
			//printf("%d %d\n",u,v);
			if (graph2[u][v]==0)
			{
				cost[u][v]*=50;
				uses[u][v]=1;
			}
			else
			{
				graph[u][v]=graph2[u][v];
				cost[u][v]=cost2[u][v];
				uses[u][v]=0;
			}
		}
		
		res=my_works();
		
		/*for (i=0;i<res.size();++i)
		{	u=ed[ed_id[res[i]]].u,v=ed[ed_id[res[i]]].v;
			if (sc==1)
				fprintf(stderr,"%d|",org[v]);
		}*/
		update(former_ans.front(),res);
		former_ans.pop_front();
	}
	printf("%d %d\n",coincide,r_cost);
	for (i=0;i<r_res1.size();++i)
		record_result(WORK_PATH, r_res1[i]-1);
	for (i=0;i<r_res2.size();++i)
		record_result(BACK_PATH, r_res2[i]-1);
}
