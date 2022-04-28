'auto' is a bash script. 
You can run it on uglogin.ecs.soton.ac.uk if you do not use a *nix system. 

To use:
Put your compiled interpreter called “Stql” in the automarker directory.
For each problem N from 1 to 5, put your solution prN.stql in the subdirectory prN/ 
Run ./autoTest whilst in the automarker directory.

To add further tests of your own:
Put the input data in a subdirectory called inputK in subdirectory prN/inputs/
e.g.   prN/inputs/input5/foo.ttl and prN/inputs/input5/bar.ttl
Put the expected output data in a file called expK.txt in subdirectory prN/expected/
e.g.  prN/expected/exp5.ttl
