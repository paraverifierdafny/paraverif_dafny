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

Installation<br>
---
In our experiment, Paraverifier_Dafny tool is run on a PC server with macOS Catalina.<br>
Install Paraverifier_Dafny Environment<br>
Paraverifier_Dafny uses Ocaml 4.02.2, Dafny 3.0.0.30203, NuSMV 2.6.0, SMT solver Z3, CMurphi 5.4.9.1, python and requires serverl ocaml libraries to run, which contains:<br>
* Core<br>
* async<br>
* yojson<br>
* core_extended<br>
* cohttp<br>
* async_graphics<br>

Usage<br>
---
First, run the server with the following command:<br>
$ cd {path}/server<br>
$ python server -v <br>
Then, enter the example folder to run the correspoding .ml file<br>
$ cd ../example<br>
$ corebuild mutual.byte -pkg str,re2 -I src <br>
Finally, run the executable file mutual.byte to verify the mutual exclusion protocol:<br>
$ ./mutual.byte <br>
