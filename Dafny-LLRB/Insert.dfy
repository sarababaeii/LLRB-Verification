include "InternalMethod.dfy"

function insert(x: int, t: LLRB): (res: LLRB)
requires isLLRB(t)
ensures  isLLRB(res)
ensures  tset(res) == tset(t) + {x}
{
    blacken(internalInsert(x, t))
}

/* The auxiliary recursive internal insert, non-visible to users */
function internalInsert(x: int, t: LLRB): (res: LLRB)
requires isLLRB(t)
ensures  color(t) == Black ==> isLLRB(res) 
ensures  color(t) == Red   ==> (weakLLRB(res) && color(res) == Red)
ensures  bHeight(t) == bHeight(res)
ensures  tset(res) == tset(t) + {x}			
decreases height(t)
{
    match mayFlipColors(t)
        case Empty            => Node(Empty, Red, x, Empty)
        case Node(l, c, y, r) => if x < y
                                    then assert c == Red && color(t) == Black 
                                                ==> (color(t.right) == Red && isLLRB(t.left) 
                                                    && t.left.Node? && color(t.left.left) == Black);
                                         var newLeft := internalInsert(x, l);
                                         var insertedTree := Node(newLeft, c, y, r);
                                         checkColors(insertedTree)
                                    else if x > y 
                                            then assert isLLRB(l);
                                                 assert c == Red && color(t) == Black 
                                                        ==> (color(t.right) == Red && isLLRB(t.right) 
                                                            && t.right.Node? && color(t.right.right) == Black);
                                                 var newRight := internalInsert(x, r);
                                                 var insertedTree := Node(l, c, y, newRight);
                                                 checkColors(insertedTree)
                                            else t // x == y
}

/* Flipping colors if a black node has two red children */
function mayFlipColors(t: LLRB): (res: LLRB)
requires isLLRB(t)
ensures  isLLRB(res)
ensures  tset(res) == tset(t)
{
    match t
        case Empty            => Empty
        case Node(l, c, x, r) => if color(l) == Red && color(r) == Red 
                                    then calc { 
                                                isLLRB(t) && color(l) == Red && color(r) == Red;
                                                ==>  { LLRBcolorFlip1(t); }	
                                                isLLRB(colorFlip(t));
                                               }	
                                         colorFlip(t)
                                    else t
}	

/* Restoring the goodColor invariant after insertion for all nodes except the root */
function checkColors(t: LLRB): (res: LLRB)
requires BST(t)
requires t.Node?
requires balanced(t)
requires if color(t) == Black && color(t.left) == Red && t.left.Node? && color(t.left.left) == Red
         then weakLLRB(t.left) && color(t.right) == Black && color(t.left.right) == Black
         else isLLRB(t.left) 
requires isLLRB(t.right)
requires !(color(t) == Red && color(t.left) == Red && color(t.right) == Red)
requires (color(t) == Black && !(color(t.right) == Red && color(t.left) == Black) &&
             !(color(t.left) == Red && t.left.Node? && color(t.left.left) == Red))
             ==> isLLRB(t)
requires (color(t) == Red && color(t.left) == Red && color(t.right) == Black)
             ==> weakLLRB(t)
ensures res.Node? 
ensures color(t) == Black ==> (isLLRB(res) && color(res) == Black)
ensures color(t) == Red   ==> (weakLLRB(res) && color(res) == Red)
ensures tset(res) == tset(t)
{
   avoidConsecReds(leftLean(t))
}

/* Fixing t if it had two consecutive red edges */
function avoidConsecReds(t: LLRB): (res: LLRB)
requires BST(t)
requires t.Node?
requires balanced(t)
requires !(color(t) == Red && color(t.right) == Red)
requires (color(t.left) == Red && t.left.Node? && color(t.left.left) == Red)
         ==> (color(t) == Black && color(t.right) == Black && color(t.left.right) == Black)
requires (color(t) == Black && !(color(t.left) == Red && t.left.Node? && color (t.left.left) == Red)) 
         ==> isLLRB(t)
requires (color(t) == Black && color(t.left) == Red && t.left.Node? && color (t.left.left) == Red)
         ==> (weakLLRB( t.left ) && isLLRB( t.right ))
requires color(t) == Red && color(t.left) == Red ==> weakLLRB(t)
requires color(t) == Red && !(color(t.left) == Red) ==> isLLRB(t)
ensures  res.Node?
ensures  if color(t) == Red && color(t.left) == Red && t.left.Node? && color(t.left.left) == Black
            then weakLLRB(res)
            else isLLRB(res)
ensures  tset(res) == tset(t)
{
    match t
        case Node(l, c, x, r) => if color(l) == Red && l.Node? && color(l.left) == Red
                                    then rotateRight(t)
                                    else t
}

// Lemmas
lemma LLRBcolorFlip1(t: LLRB)
requires isLLRB(t) && color(t) == Black
requires t.Node? && color(t.left) == Red && color(t.right) == Red
ensures isLLRB(colorFlip(t))
{
}				
