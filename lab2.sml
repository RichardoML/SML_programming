(*
	reverse: int list -> int list
	requires: int list
	ensures: ecaluate the reverse of the input list
*)
fun reverse [] = []
	|reverse [a] = [a]
	|reverse (a::L) =  reverse L @ [a];
	(*O(n*n)*)

val  intlist = [1,2,3,4,5,6,7,8,9];
val  shortintlist = [1,2,3];
val reverse_intlist1 = reverse intlist;
(*
  tail recursion 
  reverse' int list -> int list 
  require:legal int list, init y []
  ensures: evaluate the reverse of the input list in O(n)
*)
fun reverse' ([],y) = y
  |reverse' (x::L,y) = reverse'(L,x::y);
val reverse_intlist2 = reverse' (intlist,[]);
(*
  not tail recursion
  interleave:int list*int list -> int list
  requires: no
  ensures: ements in the list in the results of alternating until the end of one of the Int list data, while remaining in the second int list data are directly attached to the tail of the resulting data
  O(n)
*)
fun interleave(A,[]) =A 
  |interleave([],A)  =A 
  |interleave(x1::L1,x2::L2) = x1::x2::interleave(L1,L2);
val interleave1 = interleave(intlist,intlist);
val interleave2 = interleave(intlist,shortintlist);
val interleave3 = interleave(shortintlist,intlist);
(*
  tail recursion
  init y []
  but O(n*n)
*)
fun interleave'(A,[],y) = y @ A
  |interleave'([],A,y)  = y @ A
  |interleave'(x1::L1,x2::L2,y) = interleave'(L1,L2,y@[x1,x2]);
val interleave4 = interleave'(intlist,shortintlist,[]);

(*
  listToTree:int list ->tree
  requires:
  ensures:evaluate a balance tree
*)
datatype 'a tree = Lf
                  |Br of 'a*'a tree*'a tree;
fun listToTree [] = Lf 
    |listToTree (x::L) = let 
                               val index = List.length L div 2
                               val llist =  List.take(L,index)
                               val rlist = List.drop(L,index)
                          in 
                               Br(x,listToTree(llist),listToTree(rlist))
                          end;
val listtotree1 = listToTree(intlist);
val listtotree2 = listToTree(shortintlist);
(*
  revT: tree -> tree 
  requires:
  ensures:reverse the tree
  height log n span log n  work n/2
*)
fun revT(T) = case T of 
              Lf => Lf
              |Br(x,ltree,rtree) => Br(x,revT(rtree),revT(ltree));
val rev1 = revT(listtotree2);

(*
  binarySearch:tree*int -> bool
  requries:
  ensures:when argument 1 is sorted,if it contain a node argument 2 ,then return true otherwise false;
*)

fun binarySearch(T,n) = case T of 
                      Lf => false
                      |Br(x,ltree,rtree) => case Int.compare(n,x) of 
                                          LESS => binarySearch(ltree,n)
                                          |EQUAL => true
                                          |GREATER => binarySearch(rtree,n);
val specialintlist = [4,2,1,3,6,5,7];
val specialtree = listToTree(specialintlist);
val find6 = binarySearch(specialtree,6);