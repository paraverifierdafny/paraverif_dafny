paraverif_dafny
====
paraverif_dafny presents an induction approach to verify the cache coherence protocol, loop program and security protocol.<br>

Dafny theory files for paper:<br>
---
*Encoding Induction Proof into Dafny*<br>
>The main safety-critical protocols proved are:<br>
>>Cache Coherence Protocol):<br>
>>>|Protocols|Rules|Scripts|Time(sec.)|Memory(KB)|
>>>|:---:|:---:|:---:|:---:|:---:|
>>>|MESI|3|4|22|87|
>>>|MOESI|3|4|19|59|
>>>|MutualEx|5|5|24|59|
>>>German|58|13|621|2433|
>>>Flash_nodata|152|60|9930|109660|
>>>Flash_data|165|62|10600|71276|

>>Security Protocol:<br>
>>>The Needham–Schroeder Public-Key Protocol<br>

>>Loop Program:<br>
>>>|Algorithm|Type|
>>>|:---:|:---:|
>>>|Maximum search (one variable)| searching|
>>>|Maximum search (two variable)| searching|
>>>|Sequential search in unsorted array| searching|
>>>|Binary search|searching
>>>|Greatest common divisor|arithmetric|
>>>|Integer division|arithmetric|
>>>|Long integer addition|arithmetric|
