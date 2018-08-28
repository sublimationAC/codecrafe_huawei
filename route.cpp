#include "route.h"
#include "lib_record.h"
#include <stdio.h>
#include <cstring>
#include <algorithm>
#include <iostream>
#include <ctime>
#include <bitset>
#include <vector>
#include <queue>
#define LL long long
#include <ctime>

const int NODENUM_SIZE = 2000 + 3;
const int SIDENUM_SIZE = 40000 + 3;
const int MUSTNODE_SIZE = 120;
const int INF = 0x3f3f3f3f;
using namespace std;

LL limit = 200000000;                 //���9��
LL limit2 = 50000000 / 1500;                 //���9/4��
LL clk = 0;
LL time_limit = 3900000;
LL time_change = 1500000;
LL time_delta = time_limit - time_change;
LL new_time = 1900000;
clock_t time_start_dfs2, time_end_dfs2,pro_begin,pro_end;

int num_Side = 0;

bool	repeat_path[SIDENUM_SIZE][2];
int 	repeat_path_val[SIDENUM_SIZE][2];
bool	check_repeat[SIDENUM_SIZE];
int 	conflict_val=100000;
vector<int> conflict_path;

int dist[NODENUM_SIZE][NODENUM_SIZE];               //��¼����֮�����
bool vit_one[NODENUM_SIZE];                   //��¼�ڵ��Ƿ����
bool vit_two[NODENUM_SIZE];                   //��¼�ڵ��Ƿ����
vector<int>link_node[NODENUM_SIZE];      //��¼�����ڽӽڵ�
vector<int>link_in[NODENUM_SIZE];
int Road_id[NODENUM_SIZE][NODENUM_SIZE];         //��¼�����֮���·��id
struct Side
{
	int LinkID, SourceID, DestinationID, Cost;

}S[SIDENUM_SIZE];

/////////// �ؾ�·��1
vector<int>must_pass_one;           //���뾭���ĵ㼯
bool must_one[NODENUM_SIZE];                //�Ƿ��߹���������ĵ�

int ans_one = INF;                  //����Ȩֵ
int Start_one, Target_one, must_num_one;         //�����յ㣬�����ؾ������Ŀ
int final_pat_one[SIDENUM_SIZE];         //��¼·��
int final_num_path_one;          //·������
struct path_detail
{
	int sum;
	int num;
	vector<int>path;
};
path_detail ANS_ONE[SIDENUM_SIZE];
path_detail ANS_two[SIDENUM_SIZE];                //·����Ϣ
int ind_ONE = 0;                //��ѡ·������
int FLAG_ONE = 0;              //�Ƿ��ҵ�·��

							   ///////// �ؾ�·��2
vector<int>must_pass_two;           //���뾭���ĵ㼯
bool must_two[NODENUM_SIZE];                //�Ƿ��߹���������ĵ�

int ans_two = INF;                  //����Ȩֵ
int Start_two, Target_two, must_num_two;         //�����յ㣬�����ؾ������Ŀ
int final_pat_two[SIDENUM_SIZE];         //��¼·��
int final_num_path_two;          //·������
int ind_two = 0;                //��ѡ·������
int FLAG_two = 0;              //�Ƿ��ҵ�·��

int nodeNum = 0;                //�ڵ�����

bool is_reverse=1;
bool is_data15;
vector<int>final_result1;
vector<int>final_result2;
int deg[NODENUM_SIZE];

bool changeCost=0;
bool path_one_have_change = 0;
bool running_two = 0;

bool cmp(path_detail a, path_detail b)
{
	return a.sum<b.sum;
}

int Atoi(char num[20])
{
	int len = strlen(num);
	int ans = 0;
	int ten = 1;
	for (int i = len - 1;i >= 0;i--)
	{
		ans += ten*(num[i] - '0');
		ten *= 10;
	}
	return ans;
}

bool visit_one[NODENUM_SIZE];
int ans_path_one[SIDENUM_SIZE], ans_path_num_one;
int tmp_path_one[SIDENUM_SIZE], tmp_path_num_one;

bool visit_two[NODENUM_SIZE];
int ans_path_two[SIDENUM_SIZE], ans_path_num_two;
int tmp_path_two[SIDENUM_SIZE], tmp_path_num_two;

//�¼ӵ�
struct node_detail
{
	int dist, id;
	int steps;
	node_detail() {};
	node_detail(int d, int i)
	{
		dist = d;
		id = i;
	}
	node_detail(int d, int i, int s)
	{
		dist = d;
		id = i;
		steps = s;
	}
	bool operator <(const node_detail& r) const {
		return dist > r.dist;
	}
};
bool cmp_node_detail(node_detail a, node_detail b)
{
	///return a.dist<b.dist;
	// if(deg[a.id]!=deg[b.id])
//       	return deg[a.id] < deg[b.id];           ///����
//   	else
//   		return a.dist<b.dist;
	if(a.dist==b.dist)
		return deg[a.id] < deg[b.id];
	else
		return a.dist<b.dist;
}


void SPFA0(int start, node_detail Dist[], int pre[], node_detail must_node[], int &nmust_node, bool must[], bool visit[]) {
	///    priority_queue<node_detail> que;
	nmust_node = 0;
	int id[NODENUM_SIZE];   //��¼����v��must_node�е��±�
	for (int i = 0;i<nodeNum;i++) {
		Dist[i].dist = INF, Dist[i].id = i;
		if (must[i])  //����Ǳ��뾭���ĵ�Ļ�
			must_node[nmust_node].dist = INF, must_node[nmust_node].id = i, id[i] = nmust_node++;
	}
	int vis[NODENUM_SIZE] = { 0 };
	Dist[start].dist = 0;
	///node_detail tmp(0,start);
	queue<int> que;
	///que.push(tmp);
	que.push(start);
	vis[start] = 1;
	while (!que.empty()) {
		int u = que.front(); que.pop();
		vis[u] = 0;
		for (int i = 0; i<(int)link_node[u].size(); i++) {
			// time_end_dfs2=clock();
			// if(time_end_dfs2 - time_start_dfs2>time_limit)
			// {
			//   return ;
			// }
			int v = link_node[u][i], c = dist[u][v];
			if (visit[v])
				continue;
			if (Dist[v].dist > Dist[u].dist + c) {  //����v
				pre[v] = u;
				Dist[v].dist = Dist[u].dist + c;
				node_detail tt(Dist[v].dist, v);
				if (must[v])          //���v�Ǳؾ����Ļ�
					must_node[id[v]] = tt;
				///que.push(tt);
				if (!vis[v]) {
					que.push(v);
					vis[v] = 1;
				}
			}
		}
	}
}


//////�Խڵ��ٵ������·
void SPFA(int start, node_detail Dist[], int pre[], node_detail must_node[], int &nmust_node, bool must[], bool visit[]) {
	///    priority_queue<node_detail> que;
	nmust_node = 0;
	int id[NODENUM_SIZE];   //��¼����v��must_node�е��±�
	for (int i = 0;i<nodeNum;i++) {
		Dist[i].dist = INF, Dist[i].id = i;
		///�¼ӵ�
		Dist[i].steps = INF;
		if (must[i])  //����Ǳ��뾭���ĵ�Ļ�
			must_node[nmust_node].dist = INF, must_node[nmust_node].id = i, id[i] = nmust_node++;
	}
	int vis[NODENUM_SIZE] = { 0 };
	Dist[start].dist = 0;
	///�¼ӵ�
	Dist[start].steps = 0;
	///node_detail tmp(0,start);
	queue<int> que;
	///que.push(tmp);
	que.push(start);
	vis[start] = 1;
	while (!que.empty()) {
		int u = que.front(); que.pop();
		vis[u] = 0;
		for (int i = 0; i<(int)link_node[u].size(); i++) {
			// time_end_dfs2=clock();
			// if(time_end_dfs2 - time_start_dfs2>time_limit)
			// {
			//   return ;
			// }
			int v = link_node[u][i], c = dist[u][v];
			if (visit[v]) continue;

			if(changeCost)
			{
				// if(running_two)
				// {
				// 	printf("************");
				// }
				if (Dist[v].steps>Dist[u].steps + 1)
				{
					pre[v] = u;
					Dist[v].dist = Dist[u].dist + c;
					Dist[v].steps = Dist[u].steps + 1;
					node_detail tt(Dist[v].dist, v, Dist[v].steps);
					if (must[v])
						must_node[id[v]] = tt;
					if (!vis[v]) {
						que.push(v);
						vis[v] = 1;
					}
				}
			}
			else{
				if (Dist[v].steps>Dist[u].steps + 1 ||
				(Dist[v].steps == Dist[u].steps + 1 && Dist[v].dist>Dist[u].dist + c))
				{
					pre[v] = u;
					Dist[v].dist = Dist[u].dist + c;
					Dist[v].steps = Dist[u].steps + 1;
					node_detail tt(Dist[v].dist, v, Dist[v].steps);
					if (must[v])
						must_node[id[v]] = tt;
					if (!vis[v]) {
						que.push(v);
						vis[v] = 1;
					}
				}
			}



		}
	}
}

bool jumpOut = 0;
void dfs2(int now_pos, int cnt, int sum, int Target, int &ans, int &ans_path_num, int &tmp_path_num, int ans_path[], int tmp_path[],
	int &FLAG, bool visit[], bool must[])
{
	time_end_dfs2 = clock();
	if(changeCost==0 && time_end_dfs2 - time_start_dfs2 > time_change)
	{
		//printf("\n first tiaojian\n");
		if(FLAG==0){
			//printf("\n second tiaojian time_change is %lld\n",time_change);
			changeCost = 1;
			jumpOut = 1;
			return ;
		}
	}
	if(jumpOut)
		return ;
	if (time_end_dfs2 - time_start_dfs2>time_limit)
	{
		return;
	}
	//     clk++;
	//     if(clk>limit2)
	//     {
	//         //printf("^^^^^%lld^^^^",clk);
	//         if(FLAG==0){
	//                 printf("NA\n");
	// //        print_time("END-nofind");
	//         return ;
	//        // printf("NA");
	//        // exit(0);
	//         }
	//         return ;
	//     }
	if (now_pos == Target&&cnt == 0)
	{
		if (sum<ans)
		{
			ans = sum;
			ans_path_num = tmp_path_num;
			printf("Cost is %d: ", ans);
			for (int i = 0;i<ans_path_num;i++) {
				ans_path[i] = tmp_path[i];
				printf("%d|", tmp_path[i]);
			}
			FLAG = 1;
		}
		visit[Target] = 0;
		return;
	}
	else if (now_pos == Target)
	{
		visit[Target] = 0;
		return;
	}

	int pre_node[NODENUM_SIZE];
	node_detail Dist[NODENUM_SIZE];
	pre_node[now_pos] = 0;     //���Ż�
	node_detail must_node[MUSTNODE_SIZE];    //���뾭���ĵ㼯
	int nmust_node;                //���뾭���ĵ�ĸ���
								   // if(num_Side<2302&&num_Side>1998)
	SPFA(now_pos, Dist, pre_node, must_node, nmust_node, must, visit);
								   // else
	//SPFA0(now_pos, Dist, pre_node, must_node, nmust_node, must, visit);
	//sort(Dist,Dist+nodeNum,cmp_node_detail);
	visit[now_pos] = 1;
	//����һ���Ż�zhe
	sort(must_node, must_node + nmust_node, cmp_node_detail);
    int p=min(nmust_node,5);
	for (int i = 0; i<p; i++) {            //����Ҫѭ��600��
		int nextt = must_node[i].id;
		if (must_node[i].dist == INF && !visit[nextt] && must[nextt]) {
			visit[now_pos] = 0;
			return;
		}
	}

	//for(int i=0;i<nodeNum;i++)   // now_pos -> nextt
	for (int i = 0; i<nmust_node; i++)                 //����Ҫѭ��600��
	{
		///int nextt=Dist[i].id;
		int nextt = must_node[i].id;
		if (visit[nextt])
			continue;
		if (!must[nextt])                //���Ż���
			continue;
		///if(Dist[i].dist==INF)   continue;
		if (must_node[i].dist == INF)
			continue;
		if (must_node[i].dist + sum>ans)
			continue;
		int tmp_tmp_path[NODENUM_SIZE], tmp_tmp_path_num = 0;
		int tmp_cnt = cnt;
		while (nextt != now_pos)
		{
			tmp_tmp_path[tmp_tmp_path_num++] = Road_id[pre_node[nextt]][nextt];
			visit[nextt] = 1;
			if (must[nextt])
				tmp_cnt--;
			nextt = pre_node[nextt];
		}
		int tt = tmp_path_num;
		for (int j = tmp_tmp_path_num - 1;j >= 0;j--)
			tmp_path[tmp_path_num++] = tmp_tmp_path[j];
		///sum+=Dist[i].dist;
		sum += must_node[i].dist;
		///dfs2(Dist[i].id,tmp_cnt,sum);
		//dfs2(must_node[i].id, tmp_cnt, sum);
		dfs2(must_node[i].id, tmp_cnt, sum, Target, ans, ans_path_num, tmp_path_num, ans_path, tmp_path, FLAG, visit, must);

		//����
		tmp_path_num = tt;
		///sum-=Dist[i].dist;
		sum -= must_node[i].dist;
		///nextt=Dist[i].id;
		nextt = must_node[i].id;
		while (nextt != now_pos)
		{
			visit[nextt] = 0;
			nextt = pre_node[nextt];
		}
	}
	visit[now_pos] = 0;
}


//////dp methon
int res_path_one[SIDENUM_SIZE], nres_path_one;
int res_cost_one;
bool vised_one[NODENUM_SIZE];
int dp_state_one[NODENUM_SIZE][MUSTNODE_SIZE];

int res_path_two[SIDENUM_SIZE], nres_path_two;
int res_cost_two;
bool vised_two[NODENUM_SIZE];
int dp_state_two[NODENUM_SIZE][MUSTNODE_SIZE];

bool cut(int u, int cost, int res_cost, vector<int> must_pass, int Start,
	int Target, bool vised[], int dp_state[][MUSTNODE_SIZE]) {
	if (cost >= res_cost) return true;     //����
	int num = 0;
	for (int i = 0; i<(int)must_pass.size(); i++) {
		if (must_pass[i] == Start || must_pass[i] == Target) continue;
		if (vised[must_pass[i]]) num++;
	}
	if (dp_state[u][num] == 0) {
		dp_state[u][num] = cost;
		return false;
	}
	else {
		if (dp_state[u][num]>cost) {
			dp_state[u][num] = cost;
			return false;  //ˢ��
		}
		else return true;
	}
}


int tp_path_one[SIDENUM_SIZE];
int tp_path_two[SIDENUM_SIZE];
int deep_threshold = 300;

void dfs15(int u, int cost, int deep, int visednum, bool vised[],
	int tp_path[], bool must[], int Start, int Target, int num, int &res_cost,
	int res_path[], int &nres_path, vector<int>must_pass, int dp_state[][MUSTNODE_SIZE])   //��ǰ��u�� ·������Ϊcost �������Ϊdeep ����visednum���ؾ���
{
	time_end_dfs2 = clock();
	if (time_end_dfs2 - time_start_dfs2>time_limit)
	{
		return;
	}
	if (deep > deep_threshold)
		return;
	vised[u] = true;
	tp_path[deep] = u;
	int tp_visednum = visednum;
	if (must[u] && u != Start && u != Target)
		tp_visednum++;   //����Ǳؾ���Ļ�tp_visednum+1
						 //Ԥ����֦
	if (cut(u, cost, res_cost, must_pass, Start, Target, vised, dp_state))
	{
		vised[u] = false;
		return;
	}
	if (u == Target) {   //�ҵ���һ��·��
		if (tp_visednum == num - 2 && cost<res_cost) {
			for (int i = 0; i <= deep; i++) res_path[i] = tp_path[i];
			nres_path = deep + 1;
			res_cost = cost;
		}
		vised[u] = 0;
		return;
	}
	for (int i = 0; i<(int)link_node[u].size(); i++) {
		int v = link_node[u][i];
		if (v == Target && tp_visednum != num - 2) continue;
		if (vised[v]) continue;
		dfs15(v, cost + dist[u][v], deep + 1, tp_visednum, vised, tp_path, must, Start, Target, num, res_cost, res_path, nres_path, must_pass, dp_state);
	}
	vised[u] = false;
}

void updata_confict(int id)
{
	int from=S[id].SourceID,to=S[id].DestinationID;
	// if(repeat_path_val[from][to]!=-1)
	// {
	// 	Road_id[from][to] = repeat_path[from][to];
	// 	dist[from][to] = repeat_path_val[from][to];
	// }
	// else
		dist[from][to]+=conflict_val;
}

void eliminate_conflict(int id)
{
		int from=S[id].SourceID,to=S[id].DestinationID;
	// if(repeat_path_val[from][to]!=-1)
	// {
	// 	Road_id[from][to] = repeat_path[from][to];
	// 	dist[from][to] = repeat_path_val[from][to];
	// }
	// else
		dist[from][to]-=conflict_val;
}

void eliminate_path1()
{
	for(int i=0;i<(int)final_result1.size();i++)
	{
		int id=final_result1[i];
		int from=S[id].SourceID,to=S[id].DestinationID;
		int val=dist[from][to];
		//printf("%d side ori cost is %d",id,val );
		eliminate_conflict(id);
		val=dist[from][to];
		//printf("  now cost is %d\n",val );
		check_repeat[id]=0;
	}
}

void updata_confict_path2()
{
	conflict_val=100000;
	for(int i=0;i<(int)final_result2.size();i++)
	{
		int id=final_result2[i];
		int from=S[id].SourceID,to=S[id].DestinationID;
		int val=dist[from][to];
		//printf("%d side ori cost is %d",id,val );
		updata_confict(id);
		val=dist[from][to];
		//printf("  now cost is %d\n",val );
		check_repeat[id]=1;
	}
}

void init_path_one()
{
	memset(vit_one,0,sizeof(vit_one));
	ans_one=INF;
	memset(visit_one,0,sizeof(visit_one));
	memset(ans_path_one,0,sizeof(ans_path_one));
	memset(tmp_path_one,0,sizeof(tmp_path_one));
	ans_path_num_one=tmp_path_num_one=0;
	memset(res_path_one,0,sizeof(res_path_one));
	nres_path_one=0;
	memset(dp_state_one,0,sizeof(dp_state_one));
	memset(tp_path_one,0,sizeof(tp_path_one));
	res_cost_one=0;
}
void init_path_two()
{
	memset(vit_two,0,sizeof(vit_two));
	ans_two=INF;
	memset(visit_two,0,sizeof(visit_two));
	memset(ans_path_two,0,sizeof(ans_path_two));
	memset(tmp_path_two,0,sizeof(tmp_path_two));
	ans_path_num_two=tmp_path_num_two=0;
	memset(res_path_two,0,sizeof(res_path_two));
	nres_path_two=0;
	memset(dp_state_two,0,sizeof(dp_state_two));
	memset(tp_path_two,0,sizeof(tp_path_two));
	res_cost_two=0;
}

void debug_path_val()
{
	int tpn=0;
	for(int i=0;i<(int)final_result1.size();i++)
	{
		int id=final_result1[i];
		int from=S[i].SourceID,to=S[i].DestinationID;
		int val=dist[from][to];
		if(val>conflict_val)
		{
			tpn++;

		}
		printf("%d cost is %d^^^", id,val);
	}
	printf("\nyour program have bug %d\n",tpn );
}
void updata_reSide()
{
	for(int i=0;i<(int)final_result1.size();i++)
	{
		int id=final_result1[i];
		int from = S[id].SourceID,to=S[id].DestinationID;
		if(repeat_path[from][to]!=0)
		{
			//printf("re_side is %d\n",repeat_path[from][to]-1 );
			Road_id[from][to] = repeat_path[from][to]-1;
			dist[from][to] = repeat_path_val[from][to];
		}
	}
}




#define MAX_VERTEX_NUM NODENUM_SIZE
#define g_max_vertex_num nodeNum
struct dptype {
    std::bitset <MAX_VERTEX_NUM> state;
};





dptype Fe12s[MAX_VERTEX_NUM][MAX_VERTEX_NUM];
std::vector<int> Fe12path[MAX_VERTEX_NUM][MAX_VERTEX_NUM];
int Fe12[MAX_VERTEX_NUM][MAX_VERTEX_NUM];
int Fe12c[MAX_VERTEX_NUM][MAX_VERTEX_NUM];
bool Fe12q[MAX_VERTEX_NUM][MAX_VERTEX_NUM];
std::queue<std::pair<int, int> > dpe12qu;


void dfs_you(int now_pos,int now_sum,int now_point,
			 const bitset<NODENUM_SIZE> used, int order,int sizesub){
	if(order==1)
		init_path_one();
	else
		init_path_two();
	int ccnt=sizesub-Fe12[now_pos][now_point];

	if(order==1){
		for (int i=0;i<=nodeNum;i++)
			visit_one[i]=used[i];
		dfs2(now_pos, ccnt, now_sum,
			Target_one, ans_one,
			ans_path_num_one, tmp_path_num_one,
			ans_path_one, tmp_path_one,
			FLAG_ONE, visit_one, must_one);
			if(FLAG_ONE==1)
			{

				int pre_p_num = Fe12path[now_pos][now_point].size() ,suf_p_num = ans_path_num_one ;
				final_result1.resize(pre_p_num+suf_p_num);

				printf("\npre num is %d, suf num is %d\n",pre_p_num,suf_p_num );
				if(is_reverse)
				{
					//printf("pre path\n");
					for(int i=0;i<pre_p_num;i++){
						final_result1[i] = Fe12path[now_pos][now_point][i];
						//printf("%d!!\n", final_result1[i]);
					}
					for(int i = suf_p_num - 1; i>=0;i--)
						final_result1[i] = ans_path_one[i];
				}
				else{
					for(int i=0;i<pre_p_num;i++)
						final_result1[i] = Fe12path[now_pos][now_point][i];
					for(int i=0;i<suf_p_num;i++)
						final_result1[i] = ans_path_one[i];
				}
				return;
			}
	}
	else{
		for (int i=0;i<=nodeNum;i++)
			visit_two[i]=used[i];
		dfs2(now_pos, ccnt, now_sum,
			Target_two, ans_two, ans_path_num_two,
			tmp_path_num_two, ans_path_two, tmp_path_two,
			FLAG_two, visit_two, must_two);
			if(FLAG_two==1)
			{
				int pre_p_num = Fe12path[now_pos][now_point].size() ,suf_p_num = ans_path_num_one ;
				final_result2.resize(pre_p_num+suf_p_num);
				printf("\npre num is %d, suf num is %d\n",pre_p_num,suf_p_num );
				if(is_reverse)
				{
					for(int i=0;i<pre_p_num;i++)
						final_result2[i] = Fe12path[now_pos][now_point][i];
					for(int i = suf_p_num - 1; i>=0;i--)
						final_result2[i] = ans_path_one[i];
				}
				else{
					for(int i=0;i<pre_p_num;i++)
						final_result2[i] = Fe12path[now_pos][now_point][i];
					for(int i=0;i<suf_p_num;i++)
						final_result2[i] = ans_path_one[i];
				}
				return;
			}
	}
}


std::pair<std::vector<int>, int> dpe12solve(int s, int t ,bool *subset,int sizesub,int order) {
	sizesub--;
    printf("rlglllll\n");

    //printf("%d %d\n", g_max_vertex_num,MAX_VERTEX_NUM);
    //bool *subset = g_bool_subset[which];
    int i, j, sz ;//sizesub = (int) g_subset[which].size();
    for (i = 0; i <= g_max_vertex_num; i++)
        for (j = 0; j <= g_max_vertex_num; j++) {
            Fe12[i][j] = -INF;
            Fe12c[i][j] = INF;
            Fe12q[i][j] = 0;
        }
    while (!dpe12qu.empty()) dpe12qu.pop();
    int x, aim, y, p, q, minans=0,w,Q=0,cannum=0,cutnum,cutsubnum;
    Fe12q[s][0] = 1;
    Fe12c[s][0] = 0;
    dpe12qu.push(std::make_pair(s, 0));
    Fe12s[s][0].state.reset();
    Fe12s[s][0].state[s] = 1;
    Fe12[s][0] = 0;
    Fe12path[s][0].clear();
    cutnum=g_max_vertex_num*2/3;
    cutsubnum=sizesub/20;
    while (!dpe12qu.empty()) {
        x = dpe12qu.front().first, y = dpe12qu.front().second;
        dpe12qu.pop();
        //printf("%d %d %d\n",x,y,Fe12[x][y]);
        Fe12q[x][y] = 0;
        if (Fe12[x][y]==sizesub || Fe12[x][y]==sizesub-1
        	|| Fe12[x][y]==sizesub-2 || Fe12[x][y]==sizesub-4
        	|| Fe12[x][y]==sizesub-8){
        	dfs_you(x,Fe12c[x][y],y,Fe12s[x][y].state,order,sizesub);
        	if ((order==1 && FLAG_ONE)||(order==2 && FLAG_two)){
        		puts("asdsda");
        		break;
        	}
        }
//         if (x == t) {
//             if (Fe12[x][y] == sizesub) {
//             //	puts("asd");
// //                return std::make_pair(Fe12path[x][y], Fe12c[x][y]);
//                 if (Fe12c[x][y]<Fe12c[x][minans]) minans=y;
//                 //printf("%d\n",++Q,Fe12c[x][y]);
//                 if (--cannum==0) break;
//             }
//             continue;
//         }
        //printf("%d\n",x);
        if (y>cutnum && Fe12[x][y]<cutsubnum) continue;

        for( i = 0,sz = (int)link_node[x].size();i<sz;i++)
       // for (i = 0, sz = (int) g_edges[x].size(); i < sz; i++)
        {

            aim = link_node[x][i];
            q = Fe12[x][y] + (subset[aim] ? (1) : (0));
            p = y+1;
            w =  Fe12c[x][y] + dist[x][aim];
            if(Fe12s[x][y].state[aim] == 0)
            {
                if (q > Fe12[aim][p] || (q==Fe12[aim][p] && Fe12c[aim][p]>w)) {
                    Fe12[aim][p] = q;
                    Fe12c[aim][p] = w;
                    //if (q<Fe12_history[aim][p]) Fe12_history[aim][p]=q;
                    Fe12s[aim][p] = Fe12s[x][y];
                    Fe12s[aim][p].state[aim] = 1;
                    Fe12path[aim][p] = Fe12path[x][y];
                    Fe12path[aim][p].push_back(Road_id[x][aim]);
                    if (Fe12q[aim][p] == 0) {
                        Fe12q[aim][p] = 1;
                        dpe12qu.push(std::make_pair(aim, p));
                        if (aim==t && Fe12[aim][p]==sizesub) cannum++;
                    }
                }
            }

        }



        //Fe12path[x][y].clear();
    }
    //printf("size = %d %d\n", Fe12path[t][minans].size(),minans);
    if (minans>0){

    	return std::make_pair(Fe12path[t][minans], Fe12c[t][minans]);
    }
    //printf("size = %d\n", Fe12path[t][minans].size());
    std::vector<int> empty_vector;
    empty_vector.clear();
    return std::make_pair(empty_vector, 0);
}





vector<int>Pre_path;



//��Ҫ��ɵĹ��������
void search_route(char *topo[MAX_EDGE_NUM], int edge_num, char *demand[MAX_DEMAND_NUM], int demand_num)
{
	pro_begin=clock();
	unsigned short result1[] = { 0, 1, 2 };//P'·��
	unsigned short result2[] = { 5, 6, 2 };//P''·��
	memset(repeat_path,0,sizeof(repeat_path));
	memset(repeat_path_val,0,sizeof(repeat_path_val));
	//printf("****%d\n",repeat_path[0][0] );

	for (int i = 0;i<edge_num;i++)
	{
		//   int len=strlen(topo[i]);
		int Linkid, Soureid, Destinationid, Cost;

		sscanf(topo[i], "%d , %d , %d , %d", &Linkid, &Soureid, &Destinationid, &Cost);
		//Cost=1;
		nodeNum = max(max(Destinationid, Soureid), nodeNum);
		if (is_reverse)
			swap(Destinationid, Soureid);
		if (dist[Soureid][Destinationid] != 0)
		{
		    //deg[Soureid] = 2;        ///����
			if (dist[Soureid][Destinationid]>Cost)////////////////////////���бȵ�ǰ·��С��·������ԭ·��������·�������¸�·��
			{
				//printf("re_side is %d\n",Road_id[Soureid][Destinationid] );
				repeat_path_val[Soureid][Destinationid] = dist[Soureid][Destinationid];////////////����·��
				repeat_path[Soureid][Destinationid] = Road_id[Soureid][Destinationid]+1;
				Road_id[Soureid][Destinationid] = Linkid;
				dist[Soureid][Destinationid] = Cost;

			}
			else
			{                                  /////////////////��������cost·����Ҳ�������ڱ�����Ҫ��ȡ
				if (repeat_path_val[Soureid][Destinationid] == 0)
				{
					//printf("re_side is %d\n",Linkid );
					repeat_path_val[Soureid][Destinationid] = Cost;
					repeat_path[Soureid][Destinationid] = Linkid+1;
				}
				else
				{
					if (repeat_path_val[Soureid][Destinationid]>Cost)
					{
						//printf("re_side is %d\n",Linkid );
						repeat_path_val[Soureid][Destinationid] = Cost;
						repeat_path[Soureid][Destinationid] = Linkid+1;
					}
				}
			}
		}
		else
		{
			link_node[Soureid].push_back(Destinationid);
			link_in[Destinationid].push_back(Soureid);
			Road_id[Soureid][Destinationid] = Linkid;
			// printf("$%d$",Road_id[Soureid][Destinationid]);
			dist[Soureid][Destinationid] = Cost;
			deg[Soureid] ++;    ///����
		}
		S[Linkid].Cost = Cost;
		S[Linkid].SourceID = Soureid;
		S[Linkid].DestinationID = Destinationid;
		S[Linkid].LinkID = Linkid;
		num_Side++;
	}

	int x = 0, p = 2;
	bool has = 1;
	while (1)
	{
		if (demand[0][p]<'0' || demand[0][p]>'9')
		{
			if (has)
			{
				must_pass_one.push_back(x);
				must_one[x] = 1;
			}
			x = 0;
			has = 0;
		}
		else {
			x = x * 10 + demand[0][p] - '0';
			has = 1;
		}
		if (demand[0][p] == 0)
		{
			break;
		}
		++p;
	}
	x = 0, p = 2, has = 1;
	while (1)
	{
		if (demand[1][p]<'0' || demand[1][p]>'9')
		{
			if (has)
			{
				must_pass_two.push_back(x);
				must_two[x] = 1;
			}
			x = 0;
			has = 0;
		}
		else {
			x = x * 10 + demand[1][p] - '0';
			has = 1;
		}
		if (demand[1][p] == 0)
		{
			break;
		}
		++p;
	}

	if (is_reverse) {
		swap(must_pass_one[0], must_pass_one[1]);
		swap(must_pass_two[0], must_pass_two[1]);
	}
	Start_one = must_pass_one[0], Start_two = must_pass_two[0];
	Target_one = must_pass_one[1], Target_two = must_pass_two[1];
	swap(must_pass_one[1], must_pass_one[must_pass_one.size() - 1]);
	swap(must_pass_two[1], must_pass_two[must_pass_two.size() - 1]);
	// must_pass.push_back(Target);
	vit_one[Start_one] = 1, vit_two[Start_two] = 1;
	must_num_one = must_pass_one.size(), must_num_two = must_pass_two.size();
	time_start_dfs2 = clock();

	if (is_data15)
	{
		for (int i = 0;i<(int)must_pass_one.size();i++)
		{
			printf("%d*", must_pass_one[i]);
		}
		puts("");

		memset(vised_one, 0, sizeof(vised_one));
		res_cost_one = 0x3f3f3f3f;
		dfs15(Start_one, 0, 0, 0, vised_one, tp_path_one, must_one, Start_one, Target_one, must_num_one, res_cost_one, res_path_one, nres_path_one, must_pass_one, dp_state_one);
		printf("first path is *****\n");
		printf("weight = %d\n", res_cost_one);


		final_result1.resize(nres_path_one);
		for (int i = nres_path_one - 1;i>0;i--)
		{
			int id = Road_id[res_path_one[i - 1]][res_path_one[i]];
			// result1[i] = id;
			check_repeat[id]=1;///////////////////////////////�ظ������ĵ�
			updata_confict(id);/////���¸�ֵ
			final_result1[i]=id;
			// record_result(WORK_PATH, result1[i]);
			printf("%d|", id);
		}
		puts("");

		for (int i = 0;i<(int)must_pass_two.size();i++)
		{
			printf("%d*", must_pass_two[i]);
		}
		puts("");

		memset(vised_two, 0, sizeof(vised_two));
		res_cost_two = 0x3f3f3f3f;
		dfs15(Start_two, 0, 0, 0, vised_two, tp_path_two, must_two, Start_two, Target_two, must_num_two, res_cost_two, res_path_two, nres_path_two, must_pass_two, dp_state_two);
		printf("second path is *****\n");
		printf("weight = %d\n", res_cost_two);
		int repeat_num=0;
		final_result2.resize(nres_path_two);
		for (int i = nres_path_two - 1;i>0;i--)
		{
			int id = Road_id[res_path_two[i - 1]][res_path_two[i]];
			// result2[i] = id;
			if(check_repeat[id])//////////////////////////////////����ظ�����
			{
				repeat_num++;
				conflict_path.push_back(id);
			}
			final_result2[i]=id;
			// record_result(BACK_PATH, result2[i]);
			printf("%d|", id);
		}
		puts("");
		printf("repeat_num is %d\n", repeat_num);

		init_path_one();
		debug_path_val();
		eliminate_path1();
		debug_path_val();
		updata_confict_path2();
		time_start_dfs2 = clock();


		res_cost_one = 0x3f3f3f3f;
		dfs15(Start_one, 0, 0, 0, vised_one, tp_path_one, must_one, Start_one, Target_one, must_num_one, res_cost_one, res_path_one, nres_path_one, must_pass_one, dp_state_one);
		printf("first path is *****\n");
		printf("weight = %d\n", res_cost_one);

		repeat_num=0;
		final_result1.clear();
		conflict_path.clear();
		final_result1.resize(nres_path_one);
		for (int i = nres_path_one - 1;i>0;i--)
		{
			int id = Road_id[res_path_one[i - 1]][res_path_one[i]];
			// result1[i] = id;
			if(check_repeat[id]){
				conflict_path.push_back(id);
				repeat_num++;
			}
			final_result1[i]=id;
			// record_result(WORK_PATH, result1[i]);
			printf("%d|", id);
		}
		puts("");
		printf("repeat_num is %d \n", repeat_num);
		printf("conflict_path num is %d\n",(int)conflict_path.size() );
		for(int i=0;i<(int)conflict_path.size();i++)
		{
			printf("%d**",conflict_path[i] );
		}


		// pro_end=clock();
		// cout<<"time is "<<pro_end - pro_begin<<endl;
	}
	else
	{



		for(int i=0;i<(int)must_pass_one.size();i++)
        {
            printf("%d*", must_pass_one[i]);
        }
        puts("");

        for(int i=0;i<(int)must_pass_two.size();i++)
        {
            printf("%d*", must_pass_two[i]);
        }
        puts("");

		visit_one[Start_one] = 1;
		nodeNum++;
		jumpOut = 0;



		std::pair<std::vector<int>, int> ant;
		ant = dpe12solve(Start_one,Target_one,must_one,must_pass_one.size(),1);
		if(FLAG_ONE==0)
		{
			printf("hhhhhhhhh\n");
			FLAG_ONE = 0;
		}
		else{
			printf("dp result1 is\n");
			// FLAG_ONE = 1;
			// ans_path_num_one = (ant.first.size());
			// ans_one = ant.second;
			// for(int i=0;i<ans_path_num_one;i++){
			// 	printf("%d^^^",ant.first[i]);
			// 	ans_path_one[i] = ant.first[i];
			// }

			for(int i=0;i<final_result1.size();i++)
				printf("%d^^^", final_result1[i]);

		}


		//changeCost  = 1;
		if(FLAG_ONE==0){

			dfs2(must_pass_one[0], must_num_one - 1, 0, Target_one, ans_one, ans_path_num_one, tmp_path_num_one, ans_path_one, tmp_path_one, FLAG_ONE, visit_one, must_one);


		}

		//changeCost = 1;
		if(FLAG_ONE == 0)
		{


			init_path_one();
			time_start_dfs2 = clock();
			LL tmp = time_limit;
			time_limit = time_delta*2;
			changeCost = 1;
			jumpOut = 0;
			dfs2(must_pass_one[0], must_num_one - 1, 0, Target_one, ans_one, ans_path_num_one, tmp_path_num_one, ans_path_one, tmp_path_one, FLAG_ONE, visit_one, must_one);
			time_limit = tmp;
			changeCost = 0;
			path_one_have_change = 1;
		}
		FLAG_ONE = 0;
		changeCost = 0;

		printf("first path is *****\n");
		printf("%d\n",ans_one );
		//cout << ans_one << endl;

		final_result1.resize(ans_path_num_one);
		if (is_reverse)
		{
			for (int i = ans_path_num_one - 1;i >= 0;i--)
				// for(int i=0;i<ans_path_num;i++)
			{
				int id = ans_path_one[i];
				// result1[i] = id;
				check_repeat[id]=1;							//�ظ������ĵ�
				printf("%d ", id);
				updata_confict(id);/////���¸�ֵ
				final_result1[i]=id;
				// record_result(WORK_PATH, result1[i]);
			}
			puts("");
		}
		else {
			//for(int i=ans_path_num-1;i>=0;i--)
			for (int i = 0;i<ans_path_num_one;i++)
			{
				int id = ans_path_one[i];
				// result1[i] = id;
				check_repeat[id]=1;//////////////////////////////�ظ������ĵ�
				printf("%d ", id);
				updata_confict(id);/////���¸�ֵ
				final_result1[i]=id;
				// record_result(WORK_PATH, result1[i]);
			}
			puts("");
		}

		//debug_path_val();

		std::pair<std::vector<int>, int> ant2;
		ant2 = dpe12solve(Start_two,Target_two,must_two,must_pass_two.size(),2);
		if(FLAG_two == 0)
		{
			printf("hhhhhhhhh22222\n");
			FLAG_two = 0;
		}
		else{
			printf("dp result2 is \n");
			// FLAG_two = 1;
			// ans_two = ant2.second;
			// ans_path_num_two = (ant2.first.size());
			// for(int i=0;i<ans_path_num_two;i++){
			// 	printf("%d^^^",ant2.first[i]);
			// 	ans_path_two[i] = ant2.first[i];
			// }
			for(int i=0;i<final_result2.size();i++)
				printf("%d^^^", final_result2[i]);
		}


		visit_two[Start_two] = 1;
		time_start_dfs2 = clock();

		//updata_reSide();   //�����رߵ���ȡ����������Ҽ���

		//time_end_dfs2 = clock();
		//LL delta = time_end_dfs2 - time_start_dfs2;
		//printf("\n changeCost is %d ,FLAG_two is %d,time_change is %d ,delta is %d\n",changeCost,FLAG_two ,time_change,delta);
		// changeCost = 1;
		// printf("\nFLAG_two is %d\n",FLAG_two );
		jumpOut = 0;
		changeCost = 0;
		if(FLAG_two==0)
		{



			dfs2(must_pass_two[0], must_num_two - 1, 0, Target_two, ans_two, ans_path_num_two, tmp_path_num_two, ans_path_two, tmp_path_two, FLAG_two, visit_two, must_two);


		}
		//LL test_bug=time_end_dfs2 - time_start_dfs2;
		//printf("\n waste time %lld\n",test_bug );
		//printf("\nchangeCost is %d\n",changeCost );
		if(FLAG_two == 0)
		{
			eliminate_path1();
			//printf("\n *********try changeCost %d ,time is %lld \n", changeCost ,time_end_dfs2 - time_start_dfs2);
			//running_two = 1;
			init_path_two();
			time_start_dfs2 = clock();
			LL tmp = time_limit;
			time_limit = time_delta;
			changeCost = 1;
			jumpOut = 0;
			dfs2(must_pass_two[0], must_num_two - 1, 0, Target_two, ans_two, ans_path_num_two, tmp_path_num_two, ans_path_two, tmp_path_two, FLAG_two, visit_two, must_two);
			time_limit = tmp;
			changeCost = 0;
		}
		FLAG_two = 0;

		printf("second path is *****\n");
		printf("%d\n",ans_two );
		// cout << ans_two << endl;
		int repeat_num=0;
		final_result2.resize(ans_path_num_two);
		if (is_reverse)
		{
			for (int i = ans_path_num_two - 1;i >= 0;i--)
				// for(int i=0;i<ans_path_num;i++)
			{
				int id = ans_path_two[i];
				// result2[i] = id;
				if(check_repeat[id]){
					conflict_path.push_back(id);
					repeat_num++;
				}
				printf("%d ", id);
				final_result2[i]=id;
				// record_result(BACK_PATH, result2[i]);
			}
			puts("");
		}
		else {
			//for(int i=ans_path_num-1;i>=0;i--)
			for (int i = 0;i<ans_path_num_two;i++)
			{
				int id = ans_path_two[i];
				// result2[i] = id;
				if(check_repeat[id]){
					conflict_path.push_back(id);
					repeat_num++;
				}
				printf("%d ", id);
				final_result2[i]=id;
				// record_result(BACK_PATH, result2[i]);
			}
			puts("");
		}
		printf("repeat_num is %d \n", repeat_num);
		printf("conflict_path num is %d\n",(int)conflict_path.size() );
		for(int i=0;i<(int)conflict_path.size();i++)
		{
			printf("%d**",conflict_path[i] );
		}
/*
�ܵ�����


*/
		pro_end=clock();
		printf("\n time is %ld\n",pro_end - pro_begin);
			// cout<<"\n time is "<<pro_end - pro_begin<<endl;
		if(repeat_num==0)
			goto ans_end;
		init_path_one();
		//debug_path_val();
		eliminate_path1();
		//debug_path_val();
		updata_confict_path2();
		//debug_path_val();
		time_start_dfs2 = clock();
		time_limit=new_time;//////////////////ʱ������д���ȶ

		FLAG_ONE=0;
		std::pair<std::vector<int>, int> ant_bc1;
		ant_bc1 = dpe12solve(Start_one,Target_one,must_one,must_pass_one.size(),1);
		if(FLAG_ONE == 0)
		{
			printf("hhhhhhhhh333333333\n");
			FLAG_ONE = 0;
		}
		else{
			printf("dp result1_third\n");
			// FLAG_ONE = 1;
			// ans_one = ant_bc1.second;
			// ans_path_num_one = (ant_bc1.first.size());
			// for(int i=0;i<ans_path_num_one;i++){
			// 	printf("%d^^^",ant_bc1.first[i]);
			// 	ans_path_one[i] = ant_bc1.first[i];
			// }
			for(int i=0;i<final_result1.size();i++)
				printf("%d^^^", final_result1[i]);
		}


		visit_one[Start_one] = 1;
		jumpOut = 0;
		if(path_one_have_change)
		{
			time_change = time_limit;
			changeCost = 1;
		}
		if(FLAG_ONE==0)
		{

			dfs2(must_pass_one[0], must_num_one - 1, 0, Target_one, ans_one, ans_path_num_one, tmp_path_num_one, ans_path_one, tmp_path_one, FLAG_ONE, visit_one, must_one);


		}


		printf("first path is *****\n");
		printf("%d\n",ans_one );
		// cout << ans_one << endl;

		conflict_path.clear();
		final_result1.clear();
		final_result1.resize(ans_path_num_one);
		repeat_num=0;
		if (is_reverse)
		{
			for (int i = ans_path_num_one - 1;i >= 0;i--)
				// for(int i=0;i<ans_path_num;i++)
			{
				int id = ans_path_one[i];
				// result1[i] = id;
				if(check_repeat[id])
				{
					repeat_num++;
					conflict_path.push_back(id);
				}
				// check_repeat[id]=1;							//�ظ������ĵ�
				printf("%d ", id);
				// updata_confict(id);/////���¸�ֵ
				final_result1[i]=id;
				// record_result(WORK_PATH, result1[i]);
			}
			puts("");
		}
		else {
			//for(int i=ans_path_num-1;i>=0;i--)
			for (int i = 0;i<ans_path_num_one;i++)
			{
				int id = ans_path_one[i];
				if(check_repeat[id])
				{
					repeat_num++;
					conflict_path.push_back(id);
				}
				// result1[i] = id;
				// check_repeat[id]=1;//////////////////////////////�ظ������ĵ�
				printf("%d ", id);
				// updata_confict(id);/////���¸�ֵ
				final_result1[i]=id;
				// record_result(WORK_PATH, result1[i]);
			}
			puts("");
		}




	}

ans_end:	printf("\n*************our ans following*********\n");
	if(is_reverse)
	{
		reverse(final_result1.begin(),final_result1.end());
		reverse(final_result2.begin(),final_result2.end());
	}
	printf("first path cost is %d\n",ans_one );
	for(int i=0;i<(int)final_result1.size();i++)
	{
		int id=final_result1[i];
		result1[i]=id;
		printf("%d||",id );
		record_result(WORK_PATH,result1[i]);
	}
	printf("\nsecond path cost is %d\n",ans_two );
	for(int i=0;i<(int)final_result2.size();i++)
	{
		int id=final_result2[i];
		result2[i]=id;
		printf("%d||",id );
		record_result(BACK_PATH,result2[i]);
	}
	printf("conflict_path num is %d\n", (int)conflict_path.size());
	for(int i=0;i<(int)conflict_path.size();i++)
	{
		int id=conflict_path[i];
		printf("%d&&", id);
	}
	printf("\ntotal cost is %d\n",ans_one+ans_two);



	pro_end=clock();
	printf("\n time is %ld\n",pro_end - pro_begin);
	// cout<<"time is "<<pro_end - pro_begin<<endl;
	// for (int i = 0; i < 3; i++)
	// {
	// 	record_result(WORK_PATH, result1[i]);
	// 	record_result(BACK_PATH, result2[i]);
	// }
}



