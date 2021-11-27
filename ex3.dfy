include "ex1.dfy"

module Reverse_Tree {

    import R_A = Reverse_Seq

    datatype Tree = Leaf(int) | Node (int, Tree, Tree)

    function revTree(t : Tree) : Tree {
        match t 
            case Leaf(x) => Leaf(x)
            case Node(x, t1, t2) => Node(x, revTree(t2), revTree(t1))
    }

    method TestRevTree() {
        var x := Node(2, Leaf(1), Leaf(6));
        var t := Node(3, Leaf(4), x);

        assert revTree(t) == Node( 3, Node(2, Leaf(6), Leaf(1)), Leaf(4));
        
    }

    ghost method revTreeProp(t : Tree)
        ensures revTree(revTree(t)) == t
        {
            match t {
                case Leaf(x) =>
                    calc {
                        revTree(revTree(Leaf(x)));
                            ==
                            revTree(Leaf(x));
                            ==
                            Leaf(x);
                            ==
                            t;
                    }
                case Node (x, t1, t2) =>
                    calc {
                        revTree(revTree(Node(x, t1, t2)));
                            ==
                            revTree(Node(x, revTree(t2),revTree(t1)));
                            ==
                            Node(x, revTree(revTree(t1)), revTree(revTree(t2)));
                            ==
                            Node(x, t1, t2);
                            ==
                            t;
                    }

            }
    }


    function sequencialise(t : Tree) : seq<int> {
        match t
            case Leaf(x) => [ x ]
            case Node(x, t1, t2) => sequencialise(t1) + [ x ] + sequencialise(t2)
    }

    method testSequencialise() {
        var x := Node(2, Leaf(1), Leaf(6));
        var t := Node(3, Leaf(4), x);

        assert sequencialise(t) == [4,3,1,2,6];

        var t_r := revTree(t);
        assert sequencialise(t_r) == [6,2,1,3,4]; 
    }

    ghost method lastPropertie(t : Tree)
        ensures sequencialise(revTree(t)) == R_A.revSeq(sequencialise(t))
        {
            match t {
                case Leaf(x) =>
                    calc {
                        sequencialise(revTree(Leaf(x)));
                            ==
                            [ x ];
                            ==
                            sequencialise(Leaf(x));
                            ==
                            R_A.revSeq(sequencialise(Leaf(x)));

                    }
                case Node(x, t1, t2) =>
                    calc {
                        sequencialise(revTree(Node(x, t1, t2)));
                            ==
                            sequencialise(Node(x, revTree(t2), revTree(t1)));
                            ==
                            sequencialise(revTree(t2)) + [ x ] + sequencialise(revTree(t1));
                            ==
                            R_A.revSeq(sequencialise(t2)) + [ x ] + R_A.revSeq(sequencialise(t1));
                            == 
                            R_A.revSeq(sequencialise(t2)) + R_A.revSeq([x]) + R_A.revSeq(sequencialise(t1));
                            == { R_A.DistProp([x], sequencialise(t2)); }
                            R_A.revSeq([ x ] + sequencialise(t2)) + R_A.revSeq(sequencialise(t1));
                            == { R_A.DistProp(sequencialise(t1), [x]+ sequencialise(t2)); }
                            R_A.revSeq(sequencialise(t1) + ([ x ] + sequencialise(t2)));
                            == { assert sequencialise(t1) + ([ x ] + sequencialise(t2)) == sequencialise(t1) + [ x ] + sequencialise(t2); }
                            R_A.revSeq(sequencialise(t1) + [ x ] + sequencialise(t2));
                            ==
                            R_A.revSeq(sequencialise(Node(x, t1, t2)));
                            
                            
                            

                    }
            }
        }



}