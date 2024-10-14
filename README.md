
# 


This repository contains an implementation of the algorithms described in "CFL-based Methods for Approximating Interleaved Dyck Reachability" by Giovanna Kobus Conrado and Andreas Pavlogiannis. The paper itself is an extended version of "A Better Approximation for Interleaved Dyck Reachability", published in SOAP 2024.

The algorithm is a modified version of a code created and written by Andreas Pavlogiannis, Jaco van de Pol and Adam Husted Kjelstrøm. The benchmarks and parts of the code are from the implementation of "Mutual Refinements of Context-Free Language Reachability" by Shuo Ding and Qirun Zhang.

**Quick start:** 

Make sure you have Go and Python 3 installed.

To run the code, go to ```src/main/``` and run, in the terminal,

```python3 run.py GRAMMAR``` 

Where ```GRAMMAR``` can be chosen from a set of preprogrammed grammars that were shown in the paper.

- "parity", "parity2" and "se" correspond to grammars (1), (2) and (3) from 5.1.
- "parity", "project" and "exclude" corresponds to grammars (1), (2) and (3) from 5.2.
- "on-demand" corresponds to grammar (5) from 5.3.

So, for example, to run the benchmarks with the straightforward parity condition, one must run:

```python3 run.py parity``` 

Output for each benchmark will be located in the  ```src/main/taint-out/``` folder.


## Structure

All code is stored in the ```src/main/``` folder.

```run.py``` contain the function to run the taint benchmarks. Benchmarks are located in ```src/main/taint/```.

```main.go``` contains the main function that runs the algorithms described.

The remaining files are auxiliary files defining data structures.
