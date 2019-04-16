(*
  anonymous function
*)
val double = (fn x=> 2*x)
val square = (fn x:int=> x*x)
(*
  frac:int -> int 
  requires:init y 1
  ensures:evaulate the fractorial of input 
*)
fun frac(0,y) = y
    |frac(x,y) = frac(x-1,y*x);

val fraction = (fn x=>frac(x,1))
(*
  thenAddOne : ((int->int)* int)-> int
  requires:
  ensures:transform a integer(double ,square or fraction)then add one
*)
fun thenAddOne(func,x)=func x +1;
val doublethenaddone = thenAddOne(double,4)
val squarethenaddone = thenAddOne(square,4)
val fracthenaddone = thenAddOne(fraction,4)
(*
  maplist: (int->int * int list)->int list
  requires:
  ensures:transform a interger set to another
*)

fun maplist(func,LI) = case LI of
                      [] => []
                      |(x::L) => (func x)::maplist(func,L);
val intlist = [1,2,3,4,5,6,7,8,9];
val doublemaplist = maplist(double,intlist);
val squaremaplist = maplist(square,intlist);
val fractionmaplist = maplist(fraction,intlist);

(*
  maplist' (int->int) -> (int list -> int list)
  requires:
  ensures:transform a int -> int function to a int list -> int list function 
*)
fun maplist'(func) = 
let 
  fun f[] = []
      |f(x::L) = func x::f(L)
in f
end
val doublemaplist' = maplist'(double) intlist;
val squaremaplist' = maplist'(square) intlist;
val fractionmaplist' = maplist'(fraction) intlist;

(*
  findOdd  int list -> int option 
  requires:
  ensures:
*)
datatype 'a option = NONE|SOME of 'a;
fun findOdd [] = NONE
    |findOdd (x::L) = if x mod 2 = 0  
                    then findOdd(L)
                    else SOME x;  
val evenintlist = [2,4,6,8,10];
val testfindOdd1 = findOdd intlist;
val testfindOdd2 = findOdd [];
val testfindOdd3 = findOdd evenintlist;
(*
  subsetSumOption:int list*int -> int list option
  requires:
  ensures:
*)
fun subsetSumOption ([],_) = NONE
    |subsetSumOption ([x],s) = if x=s
                             then SOME [x]
                             else NONE
    |subsetSumOption(x::L,s) = let 
                                val if_choose_x = subsetSumOption(L,s-x)
                                val if_not_choose_x = subsetSumOption(L,s)
                             in 
                                if if_choose_x = NONE
                                then if_not_choose_x
                                else SOME(x::(fn SOME (x) => x| NONE =>[])if_choose_x)
                              end;
val oddlist = [1,3,5,7,9,11,13];
val testsubset1 = subsetSumOption(intlist,17);
val testsubset2 = subsetSumOption(oddlist,49);
val testsunset3 = subsetSumOption(oddlist,100);
(*
  exists ('a -> bool) -> 'a list -> bool
  requires:
  ensures:
*)
fun exists(_,[]) = false
  |exists(p,x::L) = if p x = true
                    then true
                    else exists(p,L);
fun biggerthan4(x) = x>4;
fun biggerthan10(x) = x>10;
val testexists = exists(biggerthan4,intlist);
val testexists = exists(biggerthan10,evenintlist);
(*
  forall:('a->bool)->'a list ->bool
  requries:
  ensures:
*)
fun forall(_,[]) = false
  |forall(p,[x]) = p x
  |forall(p,x::L) = p x andalso forall(p,L);
fun lessthan20(x) = x<20;
val testforall1 = forall(biggerthan4,intlist);
val testforall2 = forall(lessthan20,intlist);
(*
   treeFilter:('a->bool) -> 'a tree ->'a option tree
   requires:
   ensures:
*)
datatype 'a tree = Leaf|Node of 'a tree * 'a *'a tree;
fun treeFilter(_,Leaf) = Leaf
    |treeFilter(p,Node(t1,v,t2)) = if  p v = true 
                                  then 
                                  Node(treeFilter(p,t1),SOME(v),treeFilter(p,t2))
                                  else
                                  Node(treeFilter(p,t1),NONE,treeFilter(p,t2));
val tree = Node(Node(Leaf,1,Leaf),2,Node(Leaf,3,Leaf));
fun biggerthan1(x) = x>1;
val testtreefilter = treeFilter(biggerthan1,tree)