module Reverse_Seq {
    /* 1.a */
    function revSeq(s : seq<int>) : seq<int>
        decreases s
        {
            if (s == []) then []
            else (revSeq(s[1..]) + [s[0]])
        }

    method TestRevSeq() {
        var y := revSeq([1,2,3]);
        assert y == [3,2,1];
    }



    /* 1.b */
    ghost method Lemma1(s: seq<int>, v : int)
        ensures revSeq(s + [v]) == [v] + revSeq(s)
    {
        if (s == []){
            calc {
                revSeq(s + [v]);
                    ==
                    revSeq([] + [v]);
                    ==
                    revSeq([v]);
                    ==
                    [] + [v];
                    ==
                    [v] + revSeq(s);
            }
        } else {
            calc {
                revSeq(s + [v]);
                    == { assert s == [ s[0] ] + s[1..]; }
                    revSeq([ s[0] ] + s[1..] + [v]);
                    == { assert ([s[0]] + s[1..] + [v])[0] == s[0];
                        assert ([s[0]] + s[1..] + [v])[1..] == s[1..] + [v]; }
                    revSeq(s[1..] + [ v ] ) + [ s[0] ];
                    ==
                    [ v ] + revSeq(s[1..]) + [ s[0] ];
                    ==
                    [ v ] + revSeq(s);
            }
        }
    }

    ghost method revSeqProp(s : seq<int>)
        ensures revSeq(revSeq(s)) == s
    {
        if (s == []) {
            calc {
                revSeq(revSeq(s));
                    ==
                    revSeq(revSeq([]));
                    == 
                    revSeq([]);
                    ==
                    [];
                    ==
                    s;
            }
        } else {
                
            calc {
                revSeq(revSeq(s));
                    ==
                    revSeq(revSeq([s[0]] + s[1..]));
                    ==
                    revSeq(revSeq(s[1..]) + [s[0]]);
                    == { Lemma1(revSeq(s[1..]), s[0]) ; }
                    [ s[0] ] + revSeq(revSeq(s[1..]));
                    ==
                    [ s[0] ] + s[1..];
                    ==
                    s;
                }
            
        }
    }

    /* 1.c */
    ghost method DistProp(s1: seq<int>, s2: seq<int>)
        ensures revSeq(s1 + s2) == revSeq(s2) + revSeq(s1)
    {
        if (s1 == []) {
            calc {
                revSeq(s1 + s2);
                    ==
                    revSeq([] + s2);
                    == { assert [] + s2 == s2; }
                    revSeq(s2);
                    ==
                    revSeq(s2) + revSeq(s1);
            }
        } else {
            calc {
                revSeq(s1 + s2);
                    == { assert [ s1[0] ] + s1[1..] == s1; }
                    revSeq([s1[0]] + s1[1..] + s2);
                    == { assert ([s1[0]] + s1[1..] + s2) == s1 + s2; }
                    revSeq([s1[0]] + (s1+s2)[1..]);
                    ==
                    revSeq((s1+s2)[1..]) + [ s1[0] ];
                    == { assert (s1+s2)[1..] == s1[1..] + s2; }
                    revSeq(s1[1..] + s2) + [ s1[0] ];
                    ==
                    revSeq(s2) + revSeq(s1[1..]) + [s1[0]];
                    ==
                    revSeq(s2) + revSeq([s1[0]] + s1[1..]);
                    ==
                    revSeq(s2) + revSeq(s1);
            }
        }
    }



}