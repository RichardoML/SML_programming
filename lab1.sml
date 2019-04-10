(*非尾递归的实现*)
(*
	mult：int list -> int
	requires:true
	ensures:mult(L) evaluate to the product of the integer s in L
*)
fun mult [] = 1
	| mult (x::L) = x * mult(L);
	
(*
	Mult: int list list -> int 
	requires:true
	ensures:Mult(R)evaluates to the products of all integers in the lists of R
*)
val intlist = [2,5,6]
val intlistlist = [[1,2],[2,4],[5]]
val test_mult = mult intlist;
fun Mult[] = 1
	|Mult(r::R) = mult(r) * Mult(R);
val test_Mult = Mult intlistlist;	

(*尾递归的实现*)
fun mult'([],a) = a
	|mult'(x::L,a) = mult'(L,a*x);

fun Mult'([],a) = a
	|Mult'(r::R,a) = Mult'(R,mult'(r，1)*a);
	
(*非尾递归*)
(*
	double:int ->int 
	requires:n>=0
	ensures:double n evaluates to 2*n
*)
fun double(0:int):int = 0
	|double n = 2 + double(n-1);
(*
	square: int -> int 
	requires: n >=0
	ensures: square n evaluates to n*n
	
	trick square(n) = square(n-1+1) = square(n-1) + 2*(n-1) + 1
*)
val doubleeight = double 8;
fun square 0 = 0
	|square n = 1 + double(n-1) + square(n-1);
val squareeight = square 8;
(*尾递归式实现*)
fun double'(0:int,a:int):int = a
	|double'(n,a) = double'(n-1,a+2);
fun square'(0:int,a:int) = a
	|square'(n,a) = square'(n-1,a+1+double'(n-1,0));
(*
	divisibleByThree:int -> bool
	requires：true 
	ensures: divisibleByThree n evaluates to true if n is a multiple of 3 and to false otherwise
*)
fun divisibleByThree(0:int):bool = true
	|divisibleByThree 1 = false
	|divisibleByThree 2 = false
	|divisibleByThree n = if(n>0) then  divisibleByThree (n-3) else divisibleByThree (n+3);
(* 
	oddP: int -> bool
	requires: n>=0
	ensures:oddP n evaluates to true iff n is odd
	
	trick：参照evenP实现，oddP(n) = oddP(n-2)
*)
val testdivisible1 = divisibleByThree 9;
val testdivisible2 = divisibleByThree ~6;
val testdivisible3 = divisibleByThree 2;

fun oddP(0:int):bool = false
	|oddP(1) = true
	|oddP(n) = oddP(n-2);
val testodd = oddP 3;
