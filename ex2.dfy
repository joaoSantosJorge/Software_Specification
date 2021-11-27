include "ex1.dfy"

module Reverse_Arr {

    import R_A = Reverse_Seq


    method reverseArr1(arr : array<int>) returns (r: array<int>)
        ensures r[..] == R_A.revSeq(arr[..])
        ensures fresh(r)
        requires arr.Length > 0
    {
        r := new int[arr.Length];
        var i := 0;
        var j := arr.Length -1;

        while (i < arr.Length)
            invariant 0 <= i <= arr.Length
            invariant j == arr.Length -i -1
            invariant r[..i] == R_A.revSeq(arr[(j+1)..]) 
            decreases arr.Length -i
        {
            r[i] := arr[arr.Length -1 -i];

            calc {
                r[..(i+1)];
                    ==
                    r[..i] + [r[i]];
                    ==
                    R_A.revSeq(arr[(j+1)..]) + [r[i]];
                    ==
                    R_A.revSeq(arr[(j+1)..]) + [arr[j]];
                    ==
                    R_A.revSeq([arr[j]] + arr[(j+1)..]);
                    ==
                    R_A.revSeq(arr[j..]);

            }

            i:= i+1;
            j:= j -1;

        }
    }
    
/* 2.b */

    method reverseArr2(arr : array<int>)
        ensures arr[..] == R_A.revSeq(old(arr[..]))
        modifies arr
    {

        var i := 0;
        var j:= arr.Length - 1;
        while (i < j)
            invariant 0 <= i <= arr.Length
            invariant j == arr.Length -i -1
            invariant forall k :: i <= k <= j ==> arr[k] == old(arr[k])
            invariant arr[..i] == R_A.revSeq(old(arr[(j+1)..]))
            invariant arr[(j+1)..] == R_A.revSeq(old(arr[..i]))
            invariant j >= i-1
            decreases j -i
        {
            assert old(arr[j]) == arr[j];

            assert i != j;
            var cur := arr[i];
            arr[i] := arr[j];
             assert old(arr[j]) == arr[i];
            arr[j] := cur;

            assert old(arr[j]) == arr[i];
            calc {
                arr[..(i+1)];
                    ==
                    arr[..i] + [arr[i]];
                    ==
                    R_A.revSeq(old(arr[(j+1)..])) + [arr[i]];
                    == { assert old(arr[j]) == arr[i]; }
                    R_A.revSeq(old(arr[(j+1)..])) + [old(arr[j])];
                    == { R_A.Lemma1(old(arr[(j+1)..]), old(arr[j] )); }
                    R_A.revSeq([old(arr[j])] + old(arr[(j+1)..]));
                    ==
                    R_A.revSeq(old(arr[j..]));
            }
            calc {
                arr[j..];
                    ==
                    [arr[j]] + arr[(j+1)..];
                    ==
                    [old(arr[i])] + arr[(j+1)..];
                    ==
                    [old(arr[i])] + R_A.revSeq(old(arr[..i]));
                    == 
                    R_A.revSeq([old(arr[i])]) + R_A.revSeq(old(arr[..i]));
                    == { R_A.DistProp(old(arr[..i]), [old(arr[i])]); }
                    R_A.revSeq(old(arr[..i]) + [old(arr[i])]);
                    == { assert old(arr[..i]) + [old(arr[i])] == old(arr[..(i+1)]); }
                    R_A.revSeq(old(arr[..(i+1)]));
            }



            i := i +1;
            j:= j -1;
        }
        assert (i == j || i == j+1);
        assert arr[..i] == R_A.revSeq(old(arr[(j+1)..]));
        assert arr[(j+1)..] == R_A.revSeq(old(arr[..i]));

        if (i == j+1) {
            calc {
                // arr[i..] == revseq(old(arr[..i]))
                //arr[..i] == revseq(old(arr[i..]))
                //arr[..] == revSeq(old(arr[..]))
                arr[..];
                    ==
                    arr[..i] + arr[i..];
                    ==
                    R_A.revSeq(old(arr[i..])) + R_A.revSeq(old(arr[..i]));
                    == { R_A.DistProp(old(arr[..i]), old(arr[i..])); }
                    R_A.revSeq(old(arr[..i]) + old(arr[i..]));
                    == { assert old(arr[..i]) + old(arr[i..]) == old(arr[..]); }
                    R_A.revSeq(old(arr[..]));
                    
            }
        } else /* i == j*/ {
            calc {
                arr[..];
                    ==
                    arr[..i] + [arr[i]] + arr[(i+1)..];
                    ==
                    R_A.revSeq(old(arr[(i+1)..])) +  R_A.revSeq(old([arr[i]])) + R_A.revSeq(old(arr[..i]));
                    ==
                    R_A.revSeq(old(arr[i..])) + R_A.revSeq(old(arr[..i]));
                    == { R_A.DistProp(old(arr[..i]), old(arr[i..])); }
                    R_A.revSeq(old(arr[..i]) + old(arr[i..]));
                    == { assert old(arr[..i]) + old(arr[i..]) == old(arr[..]); }
                    R_A.revSeq(old(arr[..]));
                    
            }
        }

    }


}