include "LLRB_Node.dfy"
include "GhostFunction.dfy"
include "InternalMethod.dfy"

/*
Delete: Find the target node is not leaf node, 
replace its value with the minimal value in right subtree.
Then delete this minimal leaf node.
If it is leaf node, we delete it.
Before do deletion, We need to ensure the node we apply deletion to is not a 2-node to maintain the black height.
*/

function delete(x: int, t: LLRB): (res: LLRB)
    requires isLLRB(t)
    ensures  isLLRB(res) 
    ensures  tset(res) == tset(t) - {x}			
{
    match t
        case Empty => Empty
        case Node(l, _, _, r) => 
            if color(l) == Black && color(r) == Black
            then blacken(delete_(x, redden(t)))
            else delete_(x,t)
}			

/*
internal method for deletion
t must not be a 2-node
*/
function delete_(x: int, t: LLRB): (res: LLRB)
    requires isLLRB(t) || (notEmpty(t) && x >= t.key && mirrorLLRB(t))
    requires notEmpty(t) ==> (color(t) == Red || color(t.left) == Red || color(t.right) == Red)
    ensures  color(t) == Black ==> color(res) == Black
    ensures  isLLRB(res)
    ensures  bHeight(res) == bHeight(t)
    ensures  tset(res) == tset(t) - {x}
    decreases card(t)
{
    match t
        case Empty => t
        case Node(l, c, y, r) =>
            if x < y
            then
                var t1 := 
                    if color(l) == Black && notEmpty(l) && color(l.left) == Black
                    then
                        assert color(r) == Black && isLLRB(t); 
                        calc { 
                            color(l) == Black && notEmpty(l) && color(l.left) == Black;
                            ==> {GoodLeft2(t);}	
                            color(ensureRedLeft(t).left) == Red || 
                            color(ensureRedLeft(t).left.left) == Red;
                        }	   
                        ensureRedLeft(t)
                    else
                        calc { 
                            !(color(l) == Black && notEmpty(l) && color(l.left) == Black);
                            ==> {GoodLeft1(t);}	
                            notEmpty(t.left) ==> (color(t.left) == Red || 
                            color(t.left.left) == Red);
                        }
                        t;
                match t1
                    case Node(ll, lc, ly, lr) => 
                        assert isLLRB(t1) && isLLRB(ll) && isLLRB(lr);
                        assert (color(delete_(x,ll)) == Black && color(lr) == Red) 
                               ==> mirrorLLRB(Node(delete_(x, ll), lc, ly, lr)); 
                        assert x != ly && !(x in tset(lr));
                        assert ((tset(ll) - {x}) + {ly}) + tset(lr) == (tset(ll) + {ly} + tset(lr)) - {x};

                        leftLean(Node(delete_(x, ll), lc, ly, lr))
                
            else // x >= y
                var t1 := 
                    if color(l) == Red && color(r) == Black
                    then
                        assert(isLLRB(t))&& isLLRB(t.left);
                        assert mirrorLLRB(rotateRight(t));
                        rotateRight(t)
                    else
                        if color(r) == Black && notEmpty(r) && color(r.left) == Black
                        then
                            ensureRedRight(t)
                        else
                            calc{ 
                                !(color(l) == Red && color(r) == Black) && 
                                !(color(r) == Black && r.Node? && color(r.left) == Black);
                                ==> {GoodRight(t);}	
                                color(r) == Red || (r.Node? ==> color(r.left) == Red);
                            }
                            t;
                match t1
                    case Node(rl, rc, ry, rr) =>
                        assert !rr.Node? || color(rr) == Red || (rr.Node? && (color(rr.right) == Red || color(rr.left) == Red));
                        if x > ry
                        then
                            assert isLLRB(rl);
                            assert !(x in tset(rl)) && x != ry;
                            assert (tset(rr)- {x}) + (tset(rl) + {ry}) == (tset(rr)+(tset(rl)+{ry}))- {x}
                                == tset(t1) - {x};
                            leftLean(Node(rl, rc, ry, delete_(x, rr)))
                        else // x == ry
                            match rr
                                case Empty => 
                                    assert rl == Empty && rc == Red;
                                    Empty
                                case Node(_, _, _, _) =>
                                    var z := minimum(rr);
                                    var rr1 := delete_(z, rr);
                                    assert z in tset(rr) && tset(rr) == tset(rr1) + {z};
                                    assert isLLRB(Node(rl, rc, z, rr1)) || 
                                        mirrorLLRB(Node(rl, rc, z, rr1));
                                    assert isLLRB(rl) && (rl.Node? ==> isLLRB(rl.left));
                                    assert tset(Node(rl, rc, z, rr1)) == tset(rl) + ({z} + tset(rr1)) 
                                        == tset(rl) + tset(rr) ==
                                        tset(t1) - {ry} == tset(t1) - {x} ;
                                    leftLean(Node(rl, rc, z, rr1))

}

function minimum(t: LLRB): int
requires isLLRB(t)
requires !(tset(t) == {})
ensures  minimum(t) in tset(t)
ensures  forall x: int :: (x in tset(t) && x != minimum(t)) ==> minimum(t) < x
{
    match t 
        case Node(l,_,m,_) =>
            match l
                case Empty         => m
                case Node(_, _, _, _) => minimum(l)
}

/*
In order not to remove a black leaf, make sure the deletion is never applied to a 2-node.
ensureRedLeft is for the case where the key to delete is in the left subtree
and do transformation to make sure the root of the left subtree is red (not a 2-node).
*/
function ensureRedLeft(t: LLRB): (res: LLRB)
    requires isLLRB(t) && notEmpty(t) && color(t) == Red
    requires notEmpty(t.left) && color(t.left.left) == Black
    ensures color(res) == Black ==> (notEmpty(res) && color(res.left) == Red)
    ensures color(res) == Red ==> (notEmpty(res) && color(res.left) == Black
            && notEmpty(res.left) && color(res.left.left) == Red
            && res.key > t.key && res.left.key == t.key)
    ensures isLLRB(res)
    ensures bHeight(res) == bHeight(t)
    ensures card(res.left) < card(t)
    ensures tset(res) == tset(t)
{
    assert isLLRB(t.right);
    var t1 := colorFlip(t);
    match t1
        case Node(l, c, y, r) =>
            if color(r.left) == Red
            then
                assert isLLRB(t.left);
                assert color(l.left) == color(l.right) == Black;
                assert isLLRB(l) && notEmpty(r.left) && isLLRB(r.left) ;
                assert notEmpty(t1.right.left) && isLLRB(t1.right.left.left)
                        && isLLRB(t1.right.left.right);
                assert isLLRB(t1.right.right);
                var r1 := rotateRight(r);
                var r2 := match r1 case Node(rl, rc, ry, rr) => 
                            if color(rr.right) == Red
                            then Node(rl, rc, ry, rotateLeft(rr))
                            else r1;
                assert isLLRB(r2.right.right);
                assert isLLRB(r2.right.left);
                var t2 := rotateLeft(Node(l, c, y, r2));
                assert isLLRB(colorFlip(t2).left) && isLLRB(colorFlip(t2).right);
                colorFlip(t2)
            else
                calc {
                    isLLRB(t) && color(t) == Red && notEmpty(t) && color(t.right) == Black && notEmpty(t.right) 
                        && color(t.right.left) == Black && color(t.left.left) == Black;
                    ==>  { LLRBcolorFlip2(t); }	
                    isLLRB(colorFlip(t));
                }
                t1
}

/*
In order not to remove a black leaf, make sure the deletion is never applied to a 2-node.
ensureRedLeft is for the case where the key to delete is the root or in the right subtree
and do transformation to make sure the root of the left subtree is red (not a 2-node).
*/
function ensureRedRight(t: LLRB): (res: LLRB)
    requires isLLRB(t) && color(t) == Red
    requires notEmpty(t) && notEmpty(t.right) && color(t.right.left) == Black
    ensures color(res) == Black ==> (isLLRB(res) && notEmpty(res) 
                && color(res.right) == Red)
    ensures color(res) == Red ==> (notEmpty(res) && isLLRB(res.left) 
                && (isLLRB(res.right) || mirrorLLRB(res.right))
                && notEmpty(res.right) && color(res.right.right) == Red) 
    ensures bHeight(res) == bHeight(t)
    ensures card(res.right) < card(t)
    ensures tset(res) == tset(t)
{
    assert isLLRB(t.left) && isLLRB(t.right) && isLLRB(t.left.left) && isLLRB(t.left.right);
    var t1 := colorFlip(t);
    if color(t1.left.left) == Red
    then
        assert notEmpty(t1.left) && isLLRB(t1.left.left);
        assert isLLRB(t1.left.right);
        assert isLLRB(t1.right);
        assert isLLRB(colorFlip(rotateRight(t1)).left);
        assert isLLRB(colorFlip(rotateRight(t1)).right.left);
        assert isLLRB(colorFlip(rotateRight(t1)).right.right);
        colorFlip(rotateRight(t1))
    else
        calc {
            isLLRB(t) && color(t) == Red && notEmpty(t) && color(t.right) == Black && notEmpty(t.right) 
                && color(t.right.left) == Black && color(t.left.left) == Black;
            ==>  { LLRBcolorFlip2(t); }
            isLLRB(colorFlip(t));
        }
        t1
}

// lemmas
// Flip a LLRB whose root is Red. The flip result is also a LLRB.
lemma LLRBcolorFlip2(t: LLRB)
requires isLLRB(t) && color(t) == Red
requires notEmpty(t) && color(t.right) == Black && notEmpty(t.right) && color(t.right.left) == Black 
            && color(t.left.left) == Black
ensures  isLLRB(colorFlip(t))
{
}

lemma GoodLeft1(t: LLRB)
requires isLLRB(t) && t.Node? 
requires color(t) == Red || color(t.left) == Red || color(t.right) == Red
requires !(color(t.left) == Black && t.left.Node? && color(t.left.left) == Black)
ensures t.left.Node? ==> (color(t.left) == Red || color(t.left.left) == Red)
{
}

lemma GoodLeft2(t: LLRB)
requires isLLRB(t) && t.Node? 
requires color(t) == Red || color(t.left) == Red || color(t.right) == Red
requires color(t.left) == Black && t.left.Node? && color(t.left.left) == Black
ensures color(ensureRedLeft(t).left) == Red || color(ensureRedLeft(t).left.left) == Red
{
    match color(ensureRedLeft(t))
        case Black =>
        case Red   =>
}

lemma GoodRight(t: LLRB)
requires isLLRB(t) || mirrorLLRB(t)
requires t.Node? && (color(t) == Red || color(t.left) == Red || color(t.right) == Red)
requires !(color(t.left) == Red && color(t.right) == Black)
requires !(color(t.right) == Black && t.right.Node? && color(t.right.left) == Black)
ensures  color(t.right) == Red || (t.right.Node? ==> color(t.right.left) == Red)
{
}
