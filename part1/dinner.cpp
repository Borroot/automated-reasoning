#include <bits/stdc++.h>
using namespace std;

typedef vector<int> vi;
typedef vector<vi> vvi;
typedef vector<vvi> vvvi;
typedef int64_t ll;
typedef vector<ll> vl;
typedef vector<vl> vvl;
typedef pair<int,int> ii;
typedef vector<ii> vii;
typedef vector<vii> vvii;
typedef queue<int> qi;

int main() {
	vi split = {0,0,0,0,0,1,1,1,1,1};
	vvi splits;
	vvvi contributes;
	do {
		if (split[0] == 1) break;
		int numCouple = 0;
		for (int i = 0; i < 5; i++) {
			numCouple += split[2*i] == split[2*i+1];
		}
		if (numCouple < 2) continue;
		vvi contributions(10, vi(10, 0));
		for (int i = 0; i < 10; i++) {
			for (int j = 0; j < 10; j++) {
				contributions[i][j] += split[i] == split[j];
			}
		}
		contributes.push_back(contributions);
		splits.push_back(split);
	} while (next_permutation(split.begin(), split.end()));
	cout << contributes.size() << endl;
	vi rounds(contributes.size(), 0);
	for (int i = 0; i < 5; i++) {
		rounds[i] = 1;
	}

	cout << "precomputation complete" << endl;

	function<bool(int,int,vvi)> dfs = [&](int depth, int last, vvi meetup){
		if (depth == 5) {
			for (int i = 0; i < 10; i++) {
				for (int j = i+1; j < 10; j++) {
					if (meetup[i][j] < 1 or meetup[i][j] > 3) return false;
				}
			}
			return true;
		}
		for (int round = last+1; round < (int) contributes.size(); round++) {
			if (depth == 1) {
				cout << round << endl;
			}
			bool isValid = true;
			vvi meetup2 = meetup;
			for (int i = 0; i < 10; i++) {
				for (int j = i+1; j < 10; j++) {
					meetup2[i][j] += contributes[round][i][j];
					isValid &= meetup2[i][j] <= 3;
				}
			}
			if (!isValid) continue;
			if (dfs(depth+1, round, meetup2)) {
				for (int i = 0; i < 10; i++) {
					cout << splits[round][i] << " ";
				} cout << endl;
				return true;
			}
		}
		return false;
	};

	vvi meetup(10, vi(10, 0));
	if (dfs(0,-1,meetup)) {
		cout << "solvable" << endl;
	} else {
		cout << "not solvable" << endl;
	}
	return 0;
}
