# minisat

Toy Python implementation of the Minisat paper: http://minisat.se/downloads/MiniSat.pdf

This version seems to work correctly, but slowly.  (Testing is done by checking the AIM CNF formulae return the correct output)

On https://toughsat.appspot.com/ you can make tough examples, e.g. 1003*241×41651.

The reference C minisat solves this in 0.17s (using 7 restarts)
This version with Pypy takes 177s (using 12 restarts)
This version with CPython takes 971s (using 13 restarts)

C minisat probably use a better high level algorithm (e.g. variable ordering based on activity) to achieve fewer restarts.

