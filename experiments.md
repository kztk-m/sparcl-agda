# Experiments 

## For 8687453 (with Agda 2.6.1)

```
$ time agda -v0 -v profile:15 Definitional.agda +RTS -H1G -A128M -s > out3.txt
1,858,412,319,984 bytes allocated in the heap
  63,144,612,472 bytes copied during GC
     405,108,536 bytes maximum residency (37 sample(s))
       1,046,808 bytes maximum slop
             386 MB total memory in use (0 MB lost due to fragmentation)

                                     Tot time (elapsed)  Avg pause  Max pause
  Gen  0      3886 colls,     0 par   109.527s  111.773s     0.0288s    0.1418s
  Gen  1        37 colls,     0 par    8.610s   8.736s     0.2361s    0.3256s

  TASKS: 4 (1 bound, 3 peak workers (3 total), using -N1)

  SPARKS: 0(0 converted, 0 overflowed, 0 dud, 0 GC'd, 0 fizzled)

  INIT    time    0.001s  (  0.004s elapsed)
  MUT     time  735.053s  (752.646s elapsed)
  GC      time  118.137s  (120.509s elapsed)
  EXIT    time    0.000s  (  0.015s elapsed)
  Total   time  853.192s  (873.174s elapsed)

  Alloc rate    2,528,268,569 bytes per MUT second

  Productivity  86.2% of total user, 86.2% of total elapsed

agda -v0 -v profile:15 Definitional.agda +RTS -H1G -A128M -s > out3.txt  853.20s user 3.16s system 98% cpu 14:33.28 total
```

```
Total                        856,231ms            
Miscellaneous                    314ms            
Termination                   10,581ms (828,099ms)
Termination.Graph            807,370ms            
Termination.Compare           10,132ms            
Termination.RecCheck              14ms            
Positivity                    12,603ms            
Deserialization                6,042ms   (7,320ms)
Deserialization.Compaction     1,278ms            
Typing                           190ms   (5,602ms)
Typing.CheckRHS                1,969ms            
Typing.With                    1,618ms            
Typing.CheckLHS                  385ms   (1,327ms)
Typing.CheckLHS.UnifyIndices     941ms            
Typing.OccursCheck               392ms            
Typing.TypeSig                   104ms            
Serialization                    497ms     (940ms)
Serialization.BinaryEncode       259ms            
Serialization.BuildInterface     147ms            
Serialization.Compress            28ms            
Parsing                           38ms     (400ms)
Parsing.OperatorsExpr            287ms            
Parsing.OperatorsPattern          74ms            
Import                           342ms            
Scoping                          232ms     (294ms)
Scoping.InverseScopeLookup        61ms            
Coverage                         215ms            
DeadCode                          51ms            
Injectivity                       29ms            
Highlighting                      24ms            
Accumulated statistics
A.Name  (fresh)         3,384
A.QName  (fresh)        1,566
Double  (fresh)            12
Integer  (fresh)            3
Node  (fresh)         121,442
Shared Term  (fresh)        0
String  (fresh)         1,380
Text  (fresh)               1
attempted-constraints   1,239
max-open-constraints       22
metas                   4,172
pointers  (fresh)           0

```

## For 93af714 (with Agda 2.6.1)

```
$ time agda -v0 -v profile:15 Definitional.agda +RTS -H1G -A128M -s > out2.txt
1,980,005,106,072 bytes allocated in the heap
  75,196,052,664 bytes copied during GC
     422,331,088 bytes maximum residency (45 sample(s))
       1,097,440 bytes maximum slop
             402 MB total memory in use (0 MB lost due to fragmentation)

                                     Tot time (elapsed)  Avg pause  Max pause
  Gen  0      4408 colls,     0 par   126.074s  129.393s     0.0294s    0.1950s
  Gen  1        45 colls,     0 par   11.805s  12.246s     0.2721s    0.5037s

  TASKS: 4 (1 bound, 3 peak workers (3 total), using -N1)

  SPARKS: 0(0 converted, 0 overflowed, 0 dud, 0 GC'd, 0 fizzled)

  INIT    time    0.001s  (  0.004s elapsed)
  MUT     time  790.022s  (814.589s elapsed)
  GC      time  137.880s  (141.639s elapsed)
  EXIT    time    0.000s  (  0.003s elapsed)
  Total   time  927.902s  (956.235s elapsed)

  Alloc rate    2,506,266,521 bytes per MUT second

  Productivity  85.1% of total user, 85.2% of total elapsed

agda -v0 -v profile:15 Definitional.agda +RTS -H1G -A128M -s > out2.txt  927.91s user 4.37s system 97% cpu 15:56.34 total
```

```
$ cat out2.txt

Total                        932,174ms
Miscellaneous                    294ms
Termination                   10,988ms (902,032ms)
Termination.Graph            880,252ms
Termination.Compare           10,763ms
Termination.RecCheck              27ms
Positivity                    14,220ms
Deserialization                5,866ms   (7,189ms)
Deserialization.Compaction     1,323ms
Typing                           149ms   (6,125ms)
Typing.CheckRHS                2,051ms
Typing.With                    1,898ms
Typing.CheckLHS                  447ms   (1,439ms)
Typing.CheckLHS.UnifyIndices     992ms
Typing.OccursCheck               477ms
Typing.TypeSig                   107ms
Serialization                    596ms   (1,052ms)
Serialization.BinaryEncode       177ms
Serialization.Sort               151ms
Serialization.BuildInterface      96ms
Serialization.Compress            30ms
Parsing                           40ms     (391ms)
Parsing.OperatorsExpr            277ms
Parsing.OperatorsPattern          73ms
Import                           319ms
Scoping                          223ms     (249ms)
Scoping.InverseScopeLookup        26ms
Coverage                         180ms
DeadCode                          65ms
Injectivity                       29ms
Highlighting                      24ms
Accumulated statistics
A.Name  (fresh)         3,540
A.QName  (fresh)        1,656
Double  (fresh)            12
Integer  (fresh)            4
Node  (fresh)         125,552
Shared Term  (fresh)        0
String  (fresh)         1,385
Text  (fresh)               1
attempted-constraints   1,275
max-open-constraints       22
metas                   4,100
pointers  (fresh)           0
```


## Old Experiments (with Agda 2.6.0.1)


```
Total                        2,201,917ms              
Miscellaneous                      141ms              
Termination                     25,203ms (2,139,370ms)
Termination.Graph            2,097,672ms              
Termination.Compare             16,210ms              
Termination.RecCheck               283ms              
Positivity                      47,761ms              
Typing                             166ms     (7,260ms)
Typing.CheckLHS                    768ms     (3,409ms)
Typing.CheckLHS.UnifyIndices     2,640ms              
Typing.With                      2,226ms              
Typing.CheckRHS                  1,146ms              
Typing.OccursCheck                 238ms              
Typing.TypeSig                      73ms              
Deserialization                  4,660ms              
Serialization                      741ms     (1,183ms)
Serialization.BinaryEncode         229ms              
Serialization.BuildInterface       171ms              
Serialization.Compress              31ms              
Parsing                             34ms       (498ms)
Parsing.OperatorsExpr              336ms              
Parsing.OperatorsPattern           127ms              
Scoping                            268ms       (299ms)
Scoping.InverseScopeLookup          30ms              
Coverage                           299ms              
DeadCode                           207ms              
Injectivity                         92ms              
Import                              86ms              
Highlighting                        64ms              

Accumulated statistics
A.Name  (fresh)           3,450
A.Name (reused)           7,872
A.QName  (fresh)          1,173
A.QName (reused)        177,327
Double  (fresh)               0
Double (reused)               0
Integer  (fresh)             12
Integer (reused)         41,269
Node  (fresh)           124,460
Node (reused)         2,855,610
Shared Term  (fresh)          0
Shared Term (reused)          0
String  (fresh)           1,242
String (reused)          65,884
Text  (fresh)                 1
Text (reused)                 0
attempted-constraints     1,292
max-open-constraints         22
max-open-metas               36
metas                     4,034
pointers  (fresh)             0
pointers (reused)             0
```
