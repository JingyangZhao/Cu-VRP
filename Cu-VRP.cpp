#include<iostream>
#include<stdio.h>
#include <fstream>
#include <string>
#include <vector>
#include <sstream>
#include <cmath>
#include <algorithm>
#include <map>
#include <ctime>
#include <iomanip>
#include <random>
#include <cstdlib> 
#include <direct.h>

using namespace std;

struct CVRPInstance {
    string name;
    string comment;
    string type;
    int dimension;
    string edge_weight_type;
    string edge_weight_format;
    int capacity;
    vector<pair<double, double>> nodes;
    vector<int> demands;
    vector<int> depot_section;
    vector<vector<double> > edge_weights;
};

CVRPInstance readCVRPFile(const string& filename) {
    CVRPInstance instance;
    ifstream infile(filename);
    string line;

    if (!infile) {
        std::cerr << "Unable to open file";
        return instance; // Return non-zero value to indicate error
    }
    
    while (getline(infile, line)) {
        istringstream iss(line);
        string keyword;
        iss >> keyword;

        if (keyword == "NAME") {
            iss.ignore(2); // igore ": "
            getline(iss, instance.name);
        } else if (keyword == "COMMENT") {
            iss.ignore(2); // igore ": "
            getline(iss, instance.comment);
        } else if (keyword == "TYPE") {
            iss.ignore(2); // igore ": "
            getline(iss, instance.type);
        } else if (keyword == "DIMENSION") {
            iss.ignore(2); // igore ": "
            iss >> instance.dimension;
        } else if (keyword == "EDGE_WEIGHT_TYPE") {
            iss.ignore(2); // igore ": "
            getline(iss, instance.edge_weight_type);
        } else if (keyword == "EDGE_WEIGHT_FORMAT:") {
            iss.ignore(1); // igore ": "
            getline(iss, instance.edge_weight_format);
        } else if (keyword == "CAPACITY") {
            iss.ignore(2); // igore ": "
            iss >> instance.capacity;
        } else if (keyword == "NODE_COORD_SECTION") {
            for (int i = 0; i < instance.dimension; ++i) {
                int id;
                double x, y;
                infile >> id >> x >> y;
                instance.nodes.push_back({x,y});
            }

            for(int i=0; i<instance.dimension; i++){
                vector<double> tem;
                for(int j=0; j<instance.dimension; j++)
                {
                    double dij = sqrt((instance.nodes[i].first-instance.nodes[j].first)*(instance.nodes[i].first-instance.nodes[j].first)
                    +(instance.nodes[i].second-instance.nodes[j].second)*(instance.nodes[i].second-instance.nodes[j].second));
                    tem.push_back(dij);
                }
                instance.edge_weights.push_back(tem);
            }
        } else if (keyword == "EDGE_WEIGHT_SECTION") {
            if(instance.edge_weight_format == "LOWER_ROW " || "LOWER_DIAG_ROW "){
                vector<vector<double>> tem(instance.dimension, vector<double>(instance.dimension));
                for(int i=0; i<instance.dimension; i++){
                    tem[i][i]=0.0;
                    for(int j=0; j<i; j++)
                    {
                        infile >> tem[i][j];
                    }
                }
                for(int i=0; i<instance.dimension; i++){
                    for(int j=i+1; j<instance.dimension; j++)
                    {
                        tem[i][j] = tem[j][i];
                    }
                    instance.edge_weights.push_back(tem[i]);
                }
            }
            else{
                cout<<"Unkown Format: "<<instance.edge_weight_format<<endl;
            }
        } else if (keyword == "DEMAND_SECTION") {
            int tem = instance.capacity;
            for (int i = 0; i < instance.dimension; ++i) {
                int id, demand;
                infile >> id >> demand;
                instance.demands.push_back(demand);
            }
        } else if (keyword == "DEPOT_SECTION") {
            int depot;
            while (infile >> depot && depot != -1) {
                instance.depot_section.push_back(depot);
            }
            if(instance.depot_section.size()>1||instance.depot_section[0]!=1) cout<<"more than one depot"<<endl;
        } else if (keyword == "EOF") {
            break;
        }
    }

    infile.close();
    return instance;
}

///the minimum weight matching algorithm
typedef long long s64;
const int INF = 2147483647;
const int MaxN = 400;
const int MaxM = 79800;
template <class T>
inline void tension(T &a, const T &b)
{
	if (b < a)
		a = b;
}
template <class T>
inline void relax(T &a, const T &b)
{
	if (b > a)
		a = b;
}
template <class T>
inline int size(const T &a)
{
	return (int)a.size();
}
inline int getint()
{
	char c;
	while (c = getchar(), '0' > c || c > '9');

	int res = c - '0';
	while (c = getchar(), '0' <= c && c <= '9')
		res = res * 10 + c - '0';
	return res;
}
const int MaxNX = MaxN + MaxN;
struct edge
{
	int v, u, w;

	edge(){}
	edge(const int &_v, const int &_u, const int &_w)
		: v(_v), u(_u), w(_w){}
};
int N, M;
edge mat[MaxNX + 1][MaxNX + 1];
int n_matches;
s64 tot_weight;
int mate[MaxNX + 1];
int lab[MaxNX + 1];
int q_n, q[MaxN];
int fa[MaxNX + 1], col[MaxNX + 1];
int slackv[MaxNX + 1];
int n_x;
int bel[MaxNX + 1], blofrom[MaxNX + 1][MaxN + 1];
vector<int> bloch[MaxNX + 1];
inline int e_delta(const edge &e) // does not work inside blossoms
{
	return lab[e.v] + lab[e.u] - mat[e.v][e.u].w * 2;
}
inline void update_slackv(int v, int x)
{
	if (!slackv[x] || e_delta(mat[v][x]) < e_delta(mat[slackv[x]][x]))
		slackv[x] = v;
}
inline void calc_slackv(int x)
{
	slackv[x] = 0;
	for (int v = 1; v <= N; v++)
		if (mat[v][x].w > 0 && bel[v] != x && col[bel[v]] == 0)
			update_slackv(v, x);
}
inline void q_push(int x)
{
	if (x <= N)
		q[q_n++] = x;
	else
	{
		for (int i = 0; i < size(bloch[x]); i++)
			q_push(bloch[x][i]);
	}
}
inline void set_mate(int xv, int xu)
{
	mate[xv] = mat[xv][xu].u;
	if (xv > N)
	{
		edge e = mat[xv][xu];
		int xr = blofrom[xv][e.v];
		int pr = find(bloch[xv].begin(), bloch[xv].end(), xr) - bloch[xv].begin();
		if (pr % 2 == 1)
		{
			reverse(bloch[xv].begin() + 1, bloch[xv].end());
			pr = size(bloch[xv]) - pr;
		}

		for (int i = 0; i < pr; i++)
			set_mate(bloch[xv][i], bloch[xv][i ^ 1]);
		set_mate(xr, xu);

		rotate(bloch[xv].begin(), bloch[xv].begin() + pr, bloch[xv].end());
	}
}
inline void set_bel(int x, int b)
{
	bel[x] = b;
	if (x > N)
	{
		for (int i = 0; i < size(bloch[x]); i++)
			set_bel(bloch[x][i], b);
	}
}
inline void augment(int xv, int xu)
{
	while (true)
	{
		int xnu = bel[mate[xv]];
		set_mate(xv, xu);
		if (!xnu)
			return;
		set_mate(xnu, bel[fa[xnu]]);
		xv = bel[fa[xnu]], xu = xnu;
	}
}
inline int get_lca(int xv, int xu)
{
	static bool book[MaxNX + 1];
	for (int x = 1; x <= n_x; x++)
		book[x] = false;
	while (xv || xu)
	{
		if (xv)
		{
			if (book[xv])
				return xv;
			book[xv] = true;
			xv = bel[mate[xv]];
			if (xv)
				xv = bel[fa[xv]];
		}
		swap(xv, xu);
	}
	return 0;
}
inline void add_blossom(int xv, int xa, int xu)
{
	int b = N + 1;
	while (b <= n_x && bel[b])
		b++;
	if (b > n_x)
		n_x++;

	lab[b] = 0;
	col[b] = 0;

	mate[b] = mate[xa];

	bloch[b].clear();
	bloch[b].push_back(xa);
	for (int x = xv; x != xa; x = bel[fa[bel[mate[x]]]])
		bloch[b].push_back(x), bloch[b].push_back(bel[mate[x]]), q_push(bel[mate[x]]);
	reverse(bloch[b].begin() + 1, bloch[b].end());
	for (int x = xu; x != xa; x = bel[fa[bel[mate[x]]]])
		bloch[b].push_back(x), bloch[b].push_back(bel[mate[x]]), q_push(bel[mate[x]]);

	set_bel(b, b);

	for (int x = 1; x <= n_x; x++)
	{
		mat[b][x].w = mat[x][b].w = 0;
		blofrom[b][x] = 0;
	}
	for (int i = 0; i < size(bloch[b]); i++)
	{
		int xs = bloch[b][i];
		for (int x = 1; x <= n_x; x++)
			if (mat[b][x].w == 0 || e_delta(mat[xs][x]) < e_delta(mat[b][x]))
				mat[b][x] = mat[xs][x], mat[x][b] = mat[x][xs];
		for (int x = 1; x <= n_x; x++)
			if (blofrom[xs][x])
				blofrom[b][x] = xs;
	}
	calc_slackv(b);
}
inline void expand_blossom1(int b) // lab[b] == 1
{
	for (int i = 0; i < size(bloch[b]); i++)
		set_bel(bloch[b][i], bloch[b][i]);

	int xr = blofrom[b][mat[b][fa[b]].v];
	int pr = find(bloch[b].begin(), bloch[b].end(), xr) - bloch[b].begin();
	if (pr % 2 == 1)
	{
		reverse(bloch[b].begin() + 1, bloch[b].end());
		pr = size(bloch[b]) - pr;
	}

	for (int i = 0; i < pr; i += 2)
	{
		int xs = bloch[b][i], xns = bloch[b][i + 1];
		fa[xs] = mat[xns][xs].v;
		col[xs] = 1, col[xns] = 0;
		slackv[xs] = 0, calc_slackv(xns);
		q_push(xns);
	}
	col[xr] = 1;
	fa[xr] = fa[b];
	for (int i = pr + 1; i < size(bloch[b]); i++)
	{
		int xs = bloch[b][i];
		col[xs] = -1;
		calc_slackv(xs);
	}

	bel[b] = 0;
}
inline void expand_blossom_final(int b) // at the final stage
{
	for (int i = 0; i < size(bloch[b]); i++)
	{
		if (bloch[b][i] > N && lab[bloch[b][i]] == 0)
			expand_blossom_final(bloch[b][i]);
		else
			set_bel(bloch[b][i], bloch[b][i]);
	}
	bel[b] = 0;
}
inline bool on_found_edge(const edge &e)
{
	int xv = bel[e.v], xu = bel[e.u];
	if (col[xu] == -1)
	{
		int nv = bel[mate[xu]];
		fa[xu] = e.v;
		col[xu] = 1, col[nv] = 0;
		slackv[xu] = slackv[nv] = 0;
		q_push(nv);
	}
	else if (col[xu] == 0)
	{
		int xa = get_lca(xv, xu);
		if (!xa)
		{
			augment(xv, xu), augment(xu, xv);
			for (int b = N + 1; b <= n_x; b++)
				if (bel[b] == b && lab[b] == 0)
					expand_blossom_final(b);
			return true;
		}
		else
			add_blossom(xv, xa, xu);
	}
	return false;
}
bool match()
{
	for (int x = 1; x <= n_x; x++)
		col[x] = -1, slackv[x] = 0;

	q_n = 0;
	for (int x = 1; x <= n_x; x++)
		if (bel[x] == x && !mate[x])
			fa[x] = 0, col[x] = 0, slackv[x] = 0, q_push(x);
	if (q_n == 0)
		return false;

	while (true)
	{
		for (int i = 0; i < q_n; i++)
		{
			int v = q[i];
			for (int u = 1; u <= N; u++)
				if (mat[v][u].w > 0 && bel[v] != bel[u])
				{
					int d = e_delta(mat[v][u]);
					if (d == 0)
					{
						if (on_found_edge(mat[v][u]))
							return true;
					}
					else if (col[bel[u]] == -1 || col[bel[u]] == 0)
						update_slackv(v, bel[u]);
				}
		}

		int d = INF;
		for (int v = 1; v <= N; v++)
			if (col[bel[v]] == 0)
				tension(d, lab[v]);
		for (int b = N + 1; b <= n_x; b++)
			if (bel[b] == b && col[b] == 1)
				tension(d, lab[b] / 2);
		for (int x = 1; x <= n_x; x++)
			if (bel[x] == x && slackv[x])
			{
				if (col[x] == -1)
					tension(d, e_delta(mat[slackv[x]][x]));
				else if (col[x] == 0)
					tension(d, e_delta(mat[slackv[x]][x]) / 2);
			}

		for (int v = 1; v <= N; v++)
		{
			if (col[bel[v]] == 0)
				lab[v] -= d;
			else if (col[bel[v]] == 1)
				lab[v] += d;
		}
		for (int b = N + 1; b <= n_x; b++)
			if (bel[b] == b)
			{
				if (col[bel[b]] == 0)
					lab[b] += d * 2;
				else if (col[bel[b]] == 1)
					lab[b] -= d * 2;
			}

		q_n = 0;
		for (int v = 1; v <= N; v++)
			if (lab[v] == 0) // all unmatched vertices' labels are zero! cheers!
				return false;
		for (int x = 1; x <= n_x; x++)
			if (bel[x] == x && slackv[x] && bel[slackv[x]] != x && e_delta(mat[slackv[x]][x]) == 0)
			{
				if (on_found_edge(mat[slackv[x]][x]))
					return true;
			}
		for (int b = N + 1; b <= n_x; b++)
			if (bel[b] == b && col[b] == 1 && lab[b] == 0)
				expand_blossom1(b);
	}
	return false;
}
void calc_max_weight_match()
{
	for (int v = 1; v <= N; v++)
		mate[v] = 0;

	n_x = N;
	n_matches = 0;
	tot_weight = 0;

	bel[0] = 0;
	for (int v = 1; v <= N; v++)
		bel[v] = v, bloch[v].clear();
	for (int v = 1; v <= N; v++)
		for (int u = 1; u <= N; u++)
			blofrom[v][u] = v == u ? v : 0;

	int w_max = 0;
	for (int v = 1; v <= N; v++)
		for (int u = 1; u <= N; u++)
			relax(w_max, mat[v][u].w);
	for (int v = 1; v <= N; v++)
		lab[v] = w_max;

	while (match())
		n_matches++;

	for (int v = 1; v <= N; v++)
		if (mate[v] && mate[v] < v)
			tot_weight += mat[v][mate[v]].w;
}
//the above functions are related to maximum weight perfect matching

//Minimum Weight Perfect Matching(MWPM)
//INPUT: team's number n, distance matrix D 
double MWPM(int numberOfOddNode, vector<vector<double> > &oddMatrix) {
    N = numberOfOddNode, M = N * (N - 1) / 2;
    for (int v = 1; v <= N; v++)
        for (int u = 1; u <= N; u++)
            mat[v][u] = edge(v, u, 0);

    for (int i = 1; i <= N; i++)
        for (int j = i + 1; j <= N; j++) {
            double w = oddMatrix[i][j];
            //converting MWPM to maximum weight perfect matching problem
            //by adding a big number to each edge's weight
            w = -w + 1000000;
            mat[i][j].w = mat[j][i].w = w;
        }
    //maximum weight matching probelm
    calc_max_weight_match();

    return (double)N / 2 * 1000000 - tot_weight;
}

void MST(vector<vector<double> > &Matrix, int &n, vector<vector<int> > &info) {
    //Using prime algorithm, start with vertex 1
    vector<bool> flag(n + 1);//recording whether vertex choosen or not
    for (int i = 1; i <= n; i++) flag[i] = false;
    vector<double > L(n + 1);
    for (int i = 1; i <= n; i++) L[i] = Matrix[1][i];
    vector<int> chosen;
    flag[1] = true;//start with vertex 1
    chosen.push_back(1);

    //searching minimum weight edge
    for (int i = 1; i <= n - 1; i++) {
        int now = 0;
        double min1 = 1e99;
        for (int j = 1; j <= n; j++) {
            if (flag[j] == false && L[j] < min1) {
                now = j;
                min1 = L[j];
            }
        }
        if (now == 0) {
            printf("mst generating error!\n");
            break;//in case that graph in not connected
        }

        flag[now] = true;
        chosen.push_back(now);
        for (int j = 1; j <= chosen.size(); j++)
            if (min1 == Matrix[now][chosen[j - 1]]) {
                info[now][chosen[j - 1]] = 1;
                info[chosen[j - 1]][now] = 1;
                break;
            }
        //updating vertices' minimum weight distance from source
        for (int j = 1; j <= n; j++) {
            if (flag[j] == false && L[j] > Matrix[now][j])
                L[j] = Matrix[now][j];
        }
    }

    vector<bool>().swap(flag);
    vector<double>().swap(L);
    vector<int>().swap(chosen);
}

struct stack {
    int top, node[1000000];
} s;

void dfs(int x, int num, vector<vector<int> > &GG) {
    int i;
    s.node[++s.top] = x;

    for (i = 0; i < num; i++) {
        if (GG[i][x] > 0) {
            GG[i][x]--;
            GG[x][i]--; //deleting this edge
            dfs(i, num, GG);
            break;
        }
    }
}

//Fleury algorithm for Euler Circuit
void fleury(int num, vector<vector<int> > &info, vector<int> &euler) {
    vector<vector<int> > GG(num, vector<int>(num));
    for (int i = 0; i < num; i++)
        for (int j = 0; j < num; j++)
            GG[i][j] = info[i + 1][j + 1];

    int x = 0;
    int i, flag;
    s.top = 0;
    s.node[s.top] = x;
    while (s.top >= 0) {
        flag = 0;
        for (i = 0; i < num; i++) {
            if (GG[s.node[s.top]][i] > 0) {
                flag = 1;
                break;
            }
        }
        if (!flag) {
            euler.push_back(s.node[s.top--] + 1);
            //printf("%d ",s.node[s.top--]+1);
        } else dfs(s.node[s.top--], num, GG);
    }

    for (int i = 0; i < num; i++) vector<int>().swap(GG[i]);
    vector<vector<int> >().swap(GG);
}

//calculate the total distance of tsp
double cal_tsp(int num, vector<vector<double> > &matrix, vector<int> &euler, int delta, vector<int> &ans) {
    int len = euler.size();
    vector<bool> flagVisit(num + 1);

    for (int i = 0; i < len; i++) {
        int position = (i + delta) % (euler.size());
        if (flagVisit[euler[position]] == false) {
            flagVisit[euler[position]] = true;
            ans.push_back(euler[position]);
        }
    }

    double sumCost = 0;
    for (int i = 0; i < ans.size() - 1; i++) {
        double cost = matrix[ans[i]][ans[i + 1]];
        sumCost += cost;
    }
    int a = ans[ans.size() - 1], b = ans[0];
    sumCost += matrix[a][b];

    vector<bool>().swap(flagVisit);
    return sumCost;
}

double seek_tsp(int num, vector<vector<double> > &matrix, vector<int> &euler, vector<int> &tourAns) {
    double minCostTour = 1e99;
    vector<int> minAns;
    vector<int> curAns;

    for (int i = 0; i < euler.size(); i++) {
        curAns.clear();
        double res = cal_tsp(num, matrix, euler, i, curAns);

        if (res < minCostTour) {
            minCostTour = res;
            minAns.clear();
            for (int curAn : curAns) {
                minAns.push_back(curAn);
            }
        }
    }
    tourAns.clear();
    for (int minAn : minAns) {
        tourAns.push_back(minAn-1);
    }
    return minCostTour;
}

//After the MWM in the 3/2-appro TSP, we can start with n different vertex
//thus seeking for a TSP with a smaller total weight
double seek(int &num, vector<vector<int> > &mst_info, vector<vector<double> > &matrix, vector<int> &tourAns) {
    
    vector<int> euler;
    fleury(num, mst_info, euler);
    euler.pop_back();

    double res = seek_tsp(num, matrix, euler, tourAns);

    //for (int i = 0; i <= num; i++) vector<int>().swap(mst_info[i]), vector<double>().swap(matrix[i]);
    vector<int>().swap(euler);
    return res;
}

double seekTSP(int &n, vector<vector<double> > &dist, vector<int> &tsptour, bool &LKH) {

    if(LKH){
        char originalDir[FILENAME_MAX];
        _getcwd(originalDir, FILENAME_MAX);

        string folder = "LKH";
        _chdir(folder.c_str());

        fstream tspFile;
        tspFile.open("tsp", ios::out);
        tspFile << "NAME : tsp\n"
                << "TYPE : TSP\n"
                << "DIMENSION : " << n << "\n"
                << "EDGE_WEIGHT_TYPE: EXPLICIT\n"
                << "EDGE_WEIGHT_FORMAT: FULL_MATRIX\n"
                << "EDGE_WEIGHT_SECTION\n";
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                tspFile << dist[i][j]*1000 << "\t";
            }
            tspFile << "\n";
        }
        tspFile.close();

        system("echo | LKH-3.exe par > NUL"); 

        fstream tourFile;
        tourFile.open("tour", ios::in);
        char temp[100];
        int readInt;
        for (int i = 0; i < 6; i++)tourFile.getline(temp, 100);
        for (int i = 0; i < n; i++) {
            tourFile >> readInt;
            tsptour.push_back(readInt-1);
        }
        tourFile.close();

        _chdir(originalDir);

        //for(auto & x: tsptour) cout<<x<<endl;

        double ans = 0.0;

        return ans;
    }
    else{
        vector<vector<double> > Matrix(n + 1, vector<double>(n + 1));

        for (int i = 1; i <= n; i++) {
            for (int j = 1; j <= n; j++) {
                Matrix[i][j] = dist[i - 1][j - 1];
            }
        }

        vector<vector<int> > mst_info(n + 1, vector<int>(n + 1));

        MST(Matrix, n, mst_info);

        //A simple test for MST(if there is a node with degree=0, then error)
        vector<int> odd_node;
        for (int i = 1; i <= n; i++) {
            int d = 0;
            for (int j = 1; j <= n; j++) {
                d += mst_info[i][j];
            }
            if (d == 0) printf("error!::::node degree = 0\n");
            else if (d % 2 == 1) odd_node.push_back(i);
        }

        int numberOfOddNode = odd_node.size();
        vector<vector<double> > oddMatrix(numberOfOddNode + 1, vector<double>(numberOfOddNode + 1));
        for (int i = 1; i <= numberOfOddNode; i++)
            for (int j = 1; j <= numberOfOddNode; j++)
                oddMatrix[i][j] = Matrix[odd_node[i - 1]][odd_node[j - 1]];

        //Seeking for a minimum perfect matching in graph HH
        MWPM(numberOfOddNode, oddMatrix);

        //Find a Eulerian Graph
        for (int i = 1; i <= numberOfOddNode; i++) mst_info[odd_node[i - 1]][odd_node[mate[i] - 1]]++;

        double tspcost = seek(n, mst_info, Matrix, tsptour);

        vector<vector<double> >().swap(Matrix);
        vector<vector<int> >().swap(mst_info);
        vector<int>().swap(odd_node);
        vector<vector<double> >().swap(oddMatrix);

        return tspcost;
    }
}

void solvecuvrp(CVRPInstance &instance, vector<double> &OurResults, bool &LKH, bool &StochasticDemand, double &a, double &b){

    int delta = 0;

    vector<int> tsptour;
    double tau = seekTSP(instance.dimension, instance.edge_weights, tsptour, LKH); // the weight of the TSP tour

    map<int, int> mp;
    for(int i=0; i<instance.dimension; i++){
        if(tsptour[i]==0) {
            delta = i;
            break;
        }
    }

    for(int i=0; i<instance.dimension; i++){
        mp[i] = tsptour[(i+delta)%instance.dimension];
        //cout<<mp[i]<<" ";
    }

    if(StochasticDemand){

        double Q;
        if(b>1e-5) Q = 4.0/1.5*a/b;
        else Q = instance.capacity; 
        
        Q = min(Q, (double)instance.capacity);

        random_device rd;
        mt19937 gen(rd());
        uniform_int_distribution<> dis(0, Q-1);

        //int up = Q/instance.greatest_cd;
        //if(up*instance.greatest_cd == Q) up-=1;
        //uniform_int_distribution<> dis(0, up);

        int IterNum = 20; // each instance runs 20 times and compute the average cost
        double TotalCost = 0.0;
        
        for(int it=0; it<IterNum; it++) 
        {
            int L = dis(gen), CurrentNode=1;

            while(CurrentNode < instance.dimension){
                double cost0 = 0.0, cost1 = 0.0;
                int TotalDemand = 0;

                for(int i=CurrentNode; i<instance.dimension; i++){
                    
                    if(L >= TotalDemand+instance.demands[mp[i]]){
                        if(TotalDemand == 0){
                            cost0 = instance.edge_weights[mp[0]][mp[i]], cost1 = L*instance.edge_weights[mp[0]][mp[i]];
                        }
                        else{
                            cost0 += instance.edge_weights[mp[i-1]][mp[i]];
                            cost1 += (L-TotalDemand)*instance.edge_weights[mp[i-1]][mp[i]];
                        }

                        TotalDemand += instance.demands[mp[i]];

                        if(i==instance.dimension-1){
                            cost0 += instance.edge_weights[mp[i]][mp[0]];
                            cost1 += (L-TotalDemand)*instance.edge_weights[mp[i]][mp[0]];

                            // if(!StochasticDemand){
                            //     cost1 -= (L-TotalDemand)*cost0; //optimize the extra load
                            //     cost1 = min(cost1, TotalDemand*cost0-cost1); //the symmetric tour with the reversed direction, cost0' = cost0, and cost1' = TotalDemand*cost0 - cost1 
                            //     //cost from CurrentNode --- i-1
                            // }
                            
                            TotalCost += a*cost0 + b*cost1;

                            CurrentNode = instance.dimension;

                            break;
                        }
                    }
                    else{
                        if(TotalDemand>0)
                        {
                            CurrentNode = i+1;

                            cost0 += instance.edge_weights[mp[i]][mp[0]];
                            cost1 += (L-TotalDemand)*instance.edge_weights[mp[i]][mp[0]];

                            // if(!StochasticDemand){
                            //     cost0 += instance.edge_weights[mp[i-1]][mp[0]];
                            //     cost1 += (L-TotalDemand)*instance.edge_weights[mp[i-1]][mp[0]];
                            //     cost1 -= (L-TotalDemand)*cost0; //optimization
                            //     cost1 = min(cost1, TotalDemand*cost0-cost1); //the symmetric tour
                            // }

                            //cost from CurrentNode --- i-1
                            TotalCost += a*cost0 + b*cost1;

                            //cost from i --- i
                            TotalCost += a*2*instance.edge_weights[mp[i]][mp[0]] + b*instance.demands[mp[i]]*instance.edge_weights[mp[i]][mp[0]];

                            L = (L-TotalDemand) + Q*ceil(1.0*(instance.demands[mp[i]]-(L-TotalDemand))/Q) - instance.demands[mp[i]];

                            break;
                        }
                        else{
                            CurrentNode = i+1;

                            TotalCost += a*2*instance.edge_weights[mp[i]][mp[0]] + b*2*L*instance.edge_weights[mp[i]][mp[0]];

                            TotalCost += a*2*instance.edge_weights[mp[i]][mp[0]] + b*instance.demands[mp[i]]*instance.edge_weights[mp[i]][mp[0]];

                            // if(!StochasticDemand){
                            //     TotalCost -= a*2*instance.edge_weights[mp[i]][mp[0]] + b*2*L*instance.edge_weights[mp[i]][mp[0]];
                            //     TotalCost += a*2*instance.edge_weights[mp[i]][mp[0]] + b*instance.demands[mp[i]]*instance.edge_weights[mp[i]][mp[0]];
                            // }

                            L = (L-TotalDemand) + Q*ceil(1.0*(instance.demands[mp[i]]-(L-TotalDemand))/Q) - instance.demands[mp[i]];
                            
                            break;
                        }
                    }
                }
            }

        }

        TotalCost = TotalCost / IterNum;
        
        OurResults.push_back(TotalCost);
    }
    else
    {
        vector<vector<int>> totaldemand(instance.dimension, vector<int>(instance.dimension));
        vector<double> partition(instance.dimension);
        vector<vector<double>> cost0(instance.dimension, vector<double>(instance.dimension));
        vector<vector<double>> cost1(instance.dimension, vector<double>(instance.dimension));
        //vector<vector<double>> cost2(instance.dimension, vector<double>(instance.dimension));
        
        for(int i=0; i<instance.dimension; i++){
            int tem = 0;
            for(int j=i; j<instance.dimension; j++)
            {
                tem += instance.demands[mp[j]];
                totaldemand[i][j] = tem;
            }
        }
        
        for(int i=0; i<instance.dimension; i++){
            for(int j=i; j<instance.dimension; j++)
            {
                if(j==i) {
                    cost0[i][j] = 2*instance.edge_weights[mp[0]][mp[i]];
                    cost1[i][j] = instance.demands[mp[j]]*instance.edge_weights[mp[0]][mp[i]];
                    //cost2[i][j] = instance.demands[mp[j]]*instance.edge_weights[mp[0]][mp[i]];
                }
                else{
                    if(totaldemand[i][j] <= instance.capacity){
                        cost0[i][j] = cost0[i][j-1] - instance.edge_weights[mp[0]][mp[j-1]] + instance.edge_weights[mp[j-1]][mp[j]] + instance.edge_weights[mp[0]][mp[j]];
                        cost1[i][j] = cost1[i][j-1] + instance.demands[mp[j]]*(cost0[i][j] - instance.edge_weights[mp[0]][mp[j]]);
                        //cost2[i][j] = totaldemand[i][j]*cost0[i][j] - cost1[i][j];
                    }
                    else{
                        cost0[i][j] = 1e99, cost1[i][j] = 1e99; //, cost2[i][j] = 1e99;
                    }
                }
            } 
        }
        // for(int i=0; i<instance.dimension; i++){
        //     for(int j=i; j<instance.dimension; j++)
        //     {
        //         cout<<cost2[i][j]<<" ";
        //     }
        //     cout<<endl;
        // }
        for(int i=0; i<instance.dimension; i++){
            partition[i] = a*cost0[0][i] + b*min(cost1[0][i], totaldemand[0][i]*cost0[0][i] - cost1[0][i]);
            if(i<=1) continue;

            for(int j=i-1; j>0; j--){
                if(totaldemand[j+1][i]<=instance.capacity)
                    partition[i] = min(partition[i], partition[j] + a*cost0[j+1][i] + b*min(cost1[j+1][i], totaldemand[j+1][i]*cost0[j+1][i] - cost1[j+1][i]));
                else
                    break;
            }
        }
        //cout<<partition[instance.dimension-1]<<endl;   

        OurResults.push_back(partition[instance.dimension-1]);

        vector<vector<int>>().swap(totaldemand);
        vector<double>().swap(partition);
        vector<vector<double>>().swap(cost0);
        vector<vector<double>>().swap(cost1);
        //vector<vector<double>>().swap(cost2);
    }

    vector<int>().swap(tsptour);
}

vector<string> filesA = {
    "Cu-VRP//A-n32-k5.vrp",
    "Cu-VRP//A-n33-k5.vrp",
    "Cu-VRP//A-n33-k6.vrp",
    "Cu-VRP//A-n34-k5.vrp",
    "Cu-VRP//A-n36-k5.vrp",
    "Cu-VRP//A-n37-k5.vrp",
    "Cu-VRP//A-n37-k6.vrp",
    "Cu-VRP//A-n38-k5.vrp",
    "Cu-VRP//A-n39-k5.vrp",
    "Cu-VRP//A-n39-k6.vrp",
    "Cu-VRP//A-n44-k7.vrp",
    "Cu-VRP//A-n45-k6.vrp",
    "Cu-VRP//A-n45-k7.vrp",
    "Cu-VRP//A-n46-k7.vrp",
    "Cu-VRP//A-n48-k7.vrp",
    "Cu-VRP//A-n53-k7.vrp",
    "Cu-VRP//A-n54-k7.vrp",
    "Cu-VRP//A-n55-k9.vrp",
    "Cu-VRP//A-n60-k9.vrp",
    "Cu-VRP//A-n61-k9.vrp",
    "Cu-VRP//A-n62-k8.vrp",
    "Cu-VRP//A-n63-k9.vrp",
    "Cu-VRP//A-n63-k10.vrp",
    "Cu-VRP//A-n64-k9.vrp",
    "Cu-VRP//A-n65-k9.vrp",
    "Cu-VRP//A-n69-k9.vrp",
    "Cu-VRP//A-n80-k10.vrp"
};

vector<string> filesB = {
    "Cu-VRP//B-n31-k5.vrp",
    "Cu-VRP//B-n34-k5.vrp",
    "Cu-VRP//B-n35-k5.vrp",
    "Cu-VRP//B-n38-k6.vrp",
    "Cu-VRP//B-n39-k5.vrp",
    "Cu-VRP//B-n41-k6.vrp",
    "Cu-VRP//B-n43-k6.vrp",
    "Cu-VRP//B-n44-k7.vrp",
    "Cu-VRP//B-n45-k5.vrp",
    "Cu-VRP//B-n45-k6.vrp",
    "Cu-VRP//B-n50-k7.vrp",
    "Cu-VRP//B-n50-k8.vrp",
    "Cu-VRP//B-n51-k7.vrp",
    "Cu-VRP//B-n52-k7.vrp",
    "Cu-VRP//B-n56-k7.vrp",
    "Cu-VRP//B-n57-k7.vrp",
    "Cu-VRP//B-n57-k9.vrp",
    "Cu-VRP//B-n63-k10.vrp",
    "Cu-VRP//B-n64-k9.vrp",
    "Cu-VRP//B-n66-k9.vrp",
    "Cu-VRP//B-n67-k10.vrp",
    "Cu-VRP//B-n68-k9.vrp",
    "Cu-VRP//B-n78-k10.vrp"
};

vector<string> filesP = {
    "Cu-VRP//P-n16-k8.vrp",
    "Cu-VRP//P-n19-k2.vrp",
    "Cu-VRP//P-n20-k2.vrp",
    "Cu-VRP//P-n21-k2.vrp",
    "Cu-VRP//P-n22-k2.vrp",
    "Cu-VRP//P-n22-k8.vrp",
    "Cu-VRP//P-n23-k8.vrp",
    "Cu-VRP//P-n40-k5.vrp",
    "Cu-VRP//P-n45-k5.vrp",
    "Cu-VRP//P-n50-k7.vrp",
    "Cu-VRP//P-n50-k8.vrp",
    "Cu-VRP//P-n50-k10.vrp",
    "Cu-VRP//P-n51-k10.vrp",
    "Cu-VRP//P-n55-k7.vrp",
    "Cu-VRP//P-n55-k8.vrp",
    "Cu-VRP//P-n55-k10.vrp",
    "Cu-VRP//P-n55-k15.vrp",
    "Cu-VRP//P-n60-k10.vrp",
    "Cu-VRP//P-n60-k15.vrp",
    "Cu-VRP//P-n65-k10.vrp",
    "Cu-VRP//P-n70-k10.vrp",
    "Cu-VRP//P-n76-k4.vrp",
    "Cu-VRP//P-n76-k5.vrp",
    "Cu-VRP//P-n101-k4.vrp"
};

vector<string> filesE = {
    "Cu-VRP//E-n7.vrp",
    "Cu-VRP//E-n13-k4.vrp",
    "Cu-VRP//E-n22-k4.vrp",
    "Cu-VRP//E-n23-k3.vrp",
    "Cu-VRP//E-n30-k3.vrp",
    "Cu-VRP//E-n31-k7.vrp",
    "Cu-VRP//E-n33-k4.vrp",
    "Cu-VRP//E-n51-k5.vrp",
    "Cu-VRP//E-n76-k7.vrp",
    "Cu-VRP//E-n76-k8.vrp",
    "Cu-VRP//E-n76-k10.vrp",
    "Cu-VRP//E-n76-k14.vrp",
    "Cu-VRP//E-n101-k8.vrp",
    "Cu-VRP//E-n101-k14.vrp",
    "Cu-VRP//Rinaldi_Y.vrp" 
};

int main() {

    vector<string> filesAll;
    
    //27 + 23 + 24 + 15
    for(auto & file: filesA) filesAll.push_back(file);
    for(auto & file: filesB) filesAll.push_back(file);
    for(auto & file: filesP) filesAll.push_back(file);
    for(auto & file: filesE) filesAll.push_back(file);

    // StochasticDemand=true means ALG.2
    // StochasticDemand=false means ALG.2+
    bool LKH = false, StochasticDemand = false;
    vector<double> OurResults, OurResultsLKH;

    clock_t s_clock, t_clock; 
	s_clock = clock();
    for (const auto& file : filesAll) {
        CVRPInstance instance = readCVRPFile(file); 

        //double a = 1, b = 0;
        double a = instance.capacity, b = 1;

        solvecuvrp(instance, OurResults, LKH, StochasticDemand, a, b);
    }
    t_clock = clock();
 	printf("The running time is:%lf\n", double(t_clock-s_clock)/CLOCKS_PER_SEC);


    // Output
    cout<<fixed<<setprecision(2);
    for(int i=0; i<OurResults.size(); i++){

        string s = filesAll[i];
        size_t start = s.find("//");
        size_t end = s.find(".vrp");
        string result = s.substr(start+2, end - start-2);

        cout<<result<<"\t"<<OurResults[i]<<endl;
    }

    system("pause");
    
    return 0;
}
