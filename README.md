# paraverif_dafny prsents an induction approach to verify the cache coherence protocol, loop program and security protocol

#how to compile the cache coherence instance:

$ cd server/

$ python server.py

new open a terminition   

$ cd example 

$ corebuild mutualEx.byte -pkg str,re2 -I src

$ ./mutualEx.byte

The generated proof scripts of cache coherence is stored in proof_scripts, and the loop program scripts is in loopprogram, the security protocol NSPK is in security protocol. 
