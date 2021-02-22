paraverif_dafny
====
>paraverif_dafny presents an induction approach to verify the cache coherence protocol, loop program and security protocol.<br>
>Dafny theory files for paper:<br>
>>*Encoding Induction Proof into Dafny*<br>
>The main theorems proved are:<br>
>>poof_scripts(cache coherence protocol)<br>
>>security protocol<br>
>>loop program<br>
#how to compile the cache coherence instance:

$ cd server/

$ python server.py

new open a terminition   

$ cd example 

$ corebuild mutualEx.byte -pkg str,re2 -I src

$ ./mutualEx.byte

The generated proof scripts of cache coherence is stored in proof_scripts, and the loop program scripts is in loopprogram, the security protocol NSPK is in security protocol. 
