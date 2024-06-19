The code was implemented using VS Code on a desktop computer running Windows.

The 'Cu-VRP' folder contains 89 files, each corresponding to one of the 89 instances.

The 'LKH' folder contains 4 files, which are used to call the LKH heuristic.

The input has already been provided, and the output includes 89 results for the 89 instances, along with the total running time.

Important parameters in the code:

① `bool LKH`: true (resp., false) means that the TSP tour is obtained by the 1.5-approximation algorithm (resp., the LKH heuristic algorithm)

② `bool StochasticDemand`: true (resp., false) means ALG.2 (resp., ALG.2+)

③ `vector<string> filesAll`: Stores the locations of the 89 instances.




