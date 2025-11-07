include "Predicate.dfy"

function rotateLeft(t: LLRB): (res: LLRB)
    requires BST(t)
    requires notEmpty(t) && notEmpty(t.right) && color(t.right) == Red
    requires balanced(t)
    requires balanced(t.right)
    ensures  BST(res)
    ensures  notEmpty(res) && notEmpty(res.left)
    ensures  balanced(res)
    ensures  res.key > t.key
    ensures  res.left.left == t.left
    ensures  res.left.right == t.right.left
    ensures  res.right == t.right.right
    ensures  color(res) == color(t)
    ensures  color(res.left) == Red
    ensures  card(res.left) < card(t)
    ensures  card(res) == card(t)
    ensures  tset(res) == tset(t)
{
    match t
        case Node(l, c, x, r) => assert(BST(r));
                                 assert r.key in tset(r);
                                 var newLeft := Node(l, Red, x, r.left);
                                 Node(newLeft, c, r.key, r.right)
}

function rotateRight(t: LLRB): (res: LLRB)
    requires BST(t) 
    requires notEmpty(t) && notEmpty(t.left) && color(t.left) == Red 
    requires balanced(t)
    requires balanced(t.left)
    ensures  BST(res)
    ensures  notEmpty(res) && notEmpty(res.right)
    ensures  balanced(res)
    ensures  res.key < t.key
    ensures  res.left == t.left.left
    ensures  res.right.left == t.left.right
    ensures  res.right.right == t.right
    ensures  color(res) == color(t)
    ensures  color(res.right) == Red
    ensures  card(res.right) < card(t)
    ensures  card(res) == card(t)
    ensures  tset(res) == tset(t)
{
    match t
        case Node(l, c, x, r) => assert BST(l);
                                 assert l.key in tset(l);
                                 var newRight := Node(l.right, Red, x, r);
                                 Node(l.left, c, l.key, newRight)            
}

function colorFlip(t: LLRB): (res: LLRB)
    requires notEmpty(t) && notEmpty(t.left) && notEmpty(t.right)
    requires color(t.left) == color(t.right) &&
             color(t) != color(t.left)
    requires BST(t) &&
             balanced(t)
    ensures  notEmpty(res) && notEmpty(res.left) && notEmpty(res.right)
    ensures  color(t) != color(res)
    ensures  color(res.left) == color(res.right) &&
             color(res) != color(res.left)  
    ensures  res.left.left   == t.left.left
    ensures  res.left.right  == t.left.right
    ensures  res.right.left  == t.right.left
    ensures  res.right.right == t.right.right
    ensures  BST(res) && 
             balanced(res)
    ensures  height(res) == height(t)
    ensures  tset(res) == tset(t)
{
    match t
        case Node(l, c, x, r) =>          
            assert BST(t);
            match l
                case Node(ll, lc, lx, lr) =>
                    assert BST(l);
                    match r
                        case Node(rl, rc, rx, rr) =>
                            assert BST(r);
                            assert BST(Node(ll, c, lx, lr)) && tset(Node(ll, c, lx, lr)) == tset(l);
                            assert BST(Node(rl, c, rx, rr)) && tset(Node(rl, c, rx, rr)) == tset(r);
                            Node(Node(ll, c, lx, lr), lc, x, Node(rl, c, rx, rr))
}

/* Fixing t if it has a black left child and a red right child, i.e. right-leaning */
function leftLean(t: LLRB): (res: LLRB)
    requires BST(t)
    requires notEmpty(t)
    requires balanced(t)
    requires if color(t) == Black && color(t.left) == Red && notEmpty(t.left) && color(t.left.left) == Red
                then weakLLRB(t.left) && color(t.right) == Black && color(t.left.right) == Black 
                else isLLRB(t.left)
    requires isLLRB(t.right)
    requires !(color(t) == Red && color(t.left) == Red && color(t.right) == Red)
    requires (color(t) == Black && !(color(t.right) == Red && color(t.left) == Black) 
                && !(color(t.left) == Red && notEmpty(t.left) && color(t.left.left) == Red))
                ==> isLLRB(t)
    requires (color(t) == Red && color(t.left) == Red && color(t.right) == Black)
                ==> weakLLRB(t)
    ensures notEmpty(res)
    ensures (color(t) == Black && !(color(t.left) == Red && notEmpty(t.left) && color (t.left.left) == Red))
                ==> isLLRB(res) 
    ensures (color(t) == Black && color(t.left) == Red && notEmpty(t.left) && color (t.left.left) == Red)
                ==> (weakLLRB(res.left) && isLLRB(res.right))
    ensures color(t) == Red ==>  weakLLRB(res) 
    ensures mirrorLLRB(t) ==> isLLRB(res)
    ensures isLLRB(t) ==> res == t
    ensures tset(res) == tset(t)
{
    match t
        case Node(l, c, x, r) => if color(r) == Red && color(l) == Black
                                    then rotateLeft(t)
                                    else t
}

function blacken(t: LLRB): LLRB
{
    match t 
        case Empty            => Empty
        case Node(l, _, y, r) => Node(l, Black, y, r)
}		
		
function redden(t: LLRB): LLRB
{
    match t 
        case Empty            => Empty
        case Node(l, _, y, r) => Node(l, Red, y, r)
}
