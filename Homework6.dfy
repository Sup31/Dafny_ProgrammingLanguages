datatype Tree<T> = Leaf | Node(Tree<T>, Tree<T>, T)
datatype List<T> = Nil | Cons(T, List<T>)

function flatten<T>(tree:Tree<T>):List<T>
{
	match tree
    case Leaf => Nil
    case Node(left, right, value) => append(Cons(value, (flatten(left))), flatten(right))  
    // preorder root left right
}

function append<T>(xs:List<T>, ys:List<T>):List<T>
ensures xs == Nil ==> append(xs, ys) == ys
ensures ys == Nil ==> append(xs, ys) == xs
{
    match xs
    case Nil => ys
    case Cons(x,xs')=> Cons(x,append(xs',ys))

}

function treeContains<T>(tree:Tree<T>, element:T):bool
{
	match tree
    case Leaf => false  //Leaf is a misnomer. It is an empty node.
    case Node(left, right, value) => 
    // if value== element then true
    // else treeContains(left, value) || treeContains(right, value)
    treeContains(left, element) || treeContains(right, element) || (value == element)
    
}

function listContains<T>(xs:List<T>, element:T):bool
{
	match xs
    case Nil => false
    case Cons(x,xs') =>
    if (x == element) then true
    else listContains(xs',element)
    
}

lemma list_append_contains<T>(xs:List<T>, ys:List<T>, element:T)
ensures listContains(append(xs, ys), element) ==  (listContains(xs, element) || listContains(ys, element))
{
    match xs
    case Nil => {}
    case Cons(x,xs') => {
        calc 
        {
            listContains(append(xs, ys), element) ;
            == listContains(Cons(x, append(xs', ys)), element) ;
            == listContains(xs, element) || listContains(ys, element) ;
        } 
    }
}

lemma sameElements<T>(tree:Tree<T>, element:T)
ensures treeContains(tree, element) <==> listContains(flatten(tree), element)
{
	match tree
    case Leaf => {}
    case Node(left, right, value) => {
        calc
        {
            treeContains(tree, element);
            == treeContains(Node(left, right, value), element);
            == (value == element) || treeContains(left, element) || treeContains(right, element) ;
            == (value == element) || listContains(flatten(left), element) || listContains(flatten(right), element);
            == listContains(Cons(value, flatten(left)), element) || listContains(flatten(right), element);
            =={ list_append_contains(Cons(value, flatten(left)), flatten(right) , element);}  //hint
                listContains(append(Cons(value, flatten(left)), flatten(right)), element);
            == listContains(flatten(tree), element);
        }
     }
}