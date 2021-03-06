(* Compilatore LKC --> SECD completo Novembre 2013  *)

(* richiamare il file: assegnamento-LKC.ml *)

datatype secdexpr = Var of string|
                    Add | Sub |  Mult | Div | Rem | Eq | Leq | 
                    Car | Cdr | Cons | Atom | Join | Rtn | Stop | Push |
                    Ap | Rap | Ld of int*int |
                    Ldc of LKC|
                    Sel of secdexpr list * secdexpr list|
                    Ldf of  secdexpr list;



(* funzioni per il calcolo dell'indirizzo di una variabile nell'ambiente *********)
fun position(x:string, a: LKC list):int =
let val VAR(w)=hd(a) in 
if x = w then 0 else 1+position(x,tl(a)) end;

fun member(x:string, l:LKC list)=
if l =[] then false else 
let val VAR(w)=hd(l) in 
if x = w then true else member(x,tl(l)) end;
  
fun location(x:string,ct:int,n:LKC list list):int*int=
  if member(x,hd(n)) then (ct,position(x,hd(n))) else
     location(x,ct+1,tl(n)); 

fun sexpr_reverse(l)=
    if l = [] then [] 
    else sexpr_reverse(tl(l))@[hd(l)];

(* togliere variabili / espressioni da una lista di Binders ***********************)

fun vars(nil)=
[] |
vars((x,y)::R)= x :: vars(R);

fun exprs(nil)=
[] |
exprs((x,y)::R)= y:: exprs(R);

fun complist(nil: LKC list, n: (LKC list) list, c: secdexpr list): secdexpr list=
(Ldc NIL)::c |
complist(x::y: LKC list ,n:  (LKC list) list,c: secdexpr list): secdexpr list 
= complist(y,n,COMP(x,n,Cons::c))

and

COMP(e:LKC, n: (LKC list) list, c: secdexpr list): secdexpr list=

case e of 
  VAR(x) => Ld(location(x,0,n))::c |
  NUM(x)=> Ldc(NUM(x))::c | 
  BOO(x)=>Ldc(BOO(x))::c  |
  STRI(x)=>Ldc(STRI(x))::c |
  NIL => Ldc(NIL)::c |
  ADD(x,y)=> COMP(y,n,COMP(x,n,Add::c))| 
  SUB(x,y)=> COMP(y,n,COMP(x,n,Sub::c))|
  MULT(x,y)=> COMP(y,n,COMP(x,n,Mult::c))|
  DIV(x,y)=> COMP(y,n,COMP(x,n,Div::c))|
  (* REM(x,y)=> COMP(y,n,COMP(x,n,Rem::c))| *)
  EQ(x,y)=> COMP(y,n,COMP(x,n,Eq::c))|
  LEQ(x,y)=> COMP(y,n,COMP(x,n,Leq::c))|
  
  CAR(x)=> COMP(x,n, Car::c) | 
  CDR(x)=> COMP(x,n, Cdr::c) | 
  CONS(x,y)=> COMP(y, n, COMP(x,n, Cons::c)) | 
  ATOM(x)=> COMP(x,n, Atom::c) | 
  
  IF(x,y,z)=> let val thenp=COMP(y,n,[Join]) and  elsep=COMP(z,n,[Join]) in
               COMP(x,n, Sel(thenp,elsep)::c) end |
  LAMBDA(x,y)=> Ldf(COMP(y,x::n,[Rtn]))::c |
  LET(body,binders)=> let
	               val var_list = vars (binders); 
	               val exp_list = exprs (binders); 
		      in
               		complist(exp_list,n,[Ldf (COMP (body, var_list::n, [Rtn]))]@[Ap]@c)
		      end |
  LETREC (body,binders) =>
            let
               val var_list = vars (binders); 
               val exp_list = exprs (binders); 
            in
               Push::complist(exp_list,var_list::n,[Ldf(COMP(body,var_list::n,[Rtn]))]@[Rap]@c)
	    end |
(* in CALL x è il nome, mentre y sono i parametri attuali, carica nello scope i paramtri per costruire l'ambiente dinamico *)
  CALL(x,y)=> complist(y,n,COMP(x,n,Ap::c))|
  _ => [];

 
(* esempi di prova *)

val C="letrec  FACT = lambda ( X ) if  eq ( X, 0 ) then 1 else  X*FACT(  X - 1 )"^
"and G = lambda ( H L ) if  eq ( nil, L ) then L else cons( H(car( L ) ),"^ 
"G ( H, cdr ( L ) )) in G ( FACT, cons(1 ,cons(2, cons(3, nil))) ) end $";

val S= "let x= 5 and y= 6 in x*3 + y * 2* x + x*y end $";


val codice_tocompile=crea_LKC(C); 
val codice_compilato=COMP(#2codice_tocompile,[],[]);  
