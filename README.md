paraverif_dafny
====
>paraverif_dafny presents an induction approach to verify the cache coherence protocol, loop program and security protocol.<br>
>Dafny theory files for paper:<br>
>>*Encoding Induction Proof into Dafny*<br>
>The main theorems proved are:<br>
>>poof_scripts(cache coherence protocol):<br>
>>>|Protocols|Rules|Scripts|Time(sec.)|Memory(KB)|
>>>|:---:|:---:|:---:|:---:|:---:|
>>>|MESI|3|4|22|87|
>>>|MOESI|3|4|19|59|
>>>|MutualEx|5|5|24|59|
>>>German|58|13|621|2433|
>>>Flash_nodata|152|60|9930|109660|
>>>Flash_data|165|62|10600|71276|
>>security protocol:<br>
>>>The Needham–Schroeder Public-Key Protocol
>>loop program:<br>
>>>|Algorithm|Type|
>>>|:---:|:---:|
>>>|Maximum search (one variable)| searching|
>>>|Maximum search (two variable)| searching|
>>>|Sequential search in unsorted array| searching|
>>>|Binary search|searching
>>>|Greatest common divisor|arithmetric|
>>>|Integer division|arithmetric|
>>>|Long integer addition|arithmetric|
#how to compile the cache coherence instance:

$ cd server/

$ python server.py

new open a terminition   

$ cd example 

$ corebuild mutualEx.byte -pkg str,re2 -I src

$ ./mutualEx.byte

The generated proof scripts of cache coherence is stored in proof_scripts, and the loop program scripts is in loopprogram, the security protocol NSPK is in security protocol. 
