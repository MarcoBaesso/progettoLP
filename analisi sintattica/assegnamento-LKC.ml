(* PARSER LispKit  incompleto Novembre 2012*)

(* richiamare l'analizzatore sintattico, ovvero il file: assegnamento-parser.ml *)

exception NOCONST;

fun ff(x):string=
case x of 
KEYWORD(a) => a |
ID(a) => a |
OP(a)=> a |
SYM(a)=> a |
STR(a)=> a |
NM(a) => "NM" |
BOOL(a)=> "BOOL" |
Nil => "Nil" (*|
_ => "oggetto non previsto"*);

fun g(nil)= "" |
g(h::t)=  ff(h) ^ g(t);

datatype LKC = 
   ADD of LKC*LKC  |
   ATOM of LKC|
   BOO of B |
   CALL of LKC * LKC list |
   CAR of LKC |
   CDR of LKC|
   CONS of LKC*LKC|
   DIV of LKC*LKC  |
   EQ of LKC*LKC |
   IF of LKC*LKC*LKC|
   LAMBDA of LKC list * LKC|
   LEQ of LKC*LKC |
   LET of LKC * (LKC*LKC) list | 
   LETREC of LKC * (LKC*LKC) list|
   MULT of LKC*LKC  |
   NIL |
   NUM of int |
   STRI of string |
   SUB of LKC*LKC |
   VAR of string ;

(* Analizzatore sintattico ****************************)
(* usare la let forma una specie di namespace evitando involontari conflitti di nome tra le funzioni definite
nelle diverse parti del programma *)

val PROG_LKC= let

fun 
Prog(KEYWORD(a)::c)=
      (* la stringa inizia con let/letrec *)
      let 
      val x1=Bind(c)
      (* hd(x1) is the KEYWORD in *)
      val x2=Exp(tl(#1x1))
      (* hd(x2) is the KEYWORD end *)
      in
	if a="let" then
		(tl(#1x2),LET(#2x2,#2x1))	
	else
	(* a=letrec *)
      		(tl(#1x2),LETREC(#2x2,#2x1))
      end  
and

(* do *)
Exp(KEYWORD("let")::c)= Prog(KEYWORD("let")::c)
|
Exp(KEYWORD("letrec")::c)= Prog(KEYWORD("letrec")::c)
|
Exp(KEYWORD("lambda")::c)=
	let
		val parametri=esp_LAMB(c)
		val corpo=Exp(#1parametri) 
	in
		(#1corpo,LAMBDA(#2parametri,#2corpo))	
	end			
|
Exp(OP("cons")::c) =
	let
		val cons=due_exp(c)
	in 
		(#1cons,CONS(#2cons,#3cons))
	end
|     
Exp(OP("car")::c) = 
	let
		val car=un_exp(c)
	in 
		(#1car,CAR(#2car))
	end
|     
Exp(OP("cdr")::c) =
	let
		val cdr=un_exp(c)
	in 
		(#1cdr,CDR(#2cdr))
	end 
|     
Exp(OP("eq")::c) =
	let
		val eq=due_exp(c)
	in 
		(#1eq,EQ(#2eq,#3eq))
	end
|     
Exp(OP("leq")::c) =
	let
		val leq=due_exp(c)
	in 
		(#1leq,LEQ(#2leq,#3leq))
	end
|     
Exp(OP("atom")::c) =
	let
		val atom=un_exp(c)
	in 
		(#1atom,ATOM(#2atom))
	end
|     
Exp(KEYWORD("if")::c) = 
  	let 
    		val test=Exp(c)
    		(* hd(x1) is the KEYWORD then *)
   		val corpothen=Exp(tl(#1test))
    		(* hd(x2) is the KEYWORD else *)
		val corpoelse=Exp(tl(#1corpothen))		
	in
		(#1corpoelse,IF(#2test,#2corpothen,#2corpoelse))
	end

| 
Exp(x)= ExpA(x)

and

(* do *)
ExpA(tokenlist)=
	let 
		val nextT=T(tokenlist)
		val nextEOne=E_one(#1nextT,#2nextT)
	in
		(#1nextEOne,#2nextEOne)
	end  

and 

(* do *)
E_one(nil,a)=(nil,a)
|
E_one(h::tail,po)=case h of
	  OP(e) => if e="+" then
			let 
				val nextT=T(tail)
				val operazione=ADD(po,#2nextT)
				val nextEOne=E_one(#1nextT,operazione)
			in
				nextEOne
			end
		   else
			if e="-" then
				let 
					val nextT=T(tail)
					val operazione=SUB(po,#2nextT)
					val nextEOne=E_one(#1nextT,operazione)
				in
					nextEOne
				end
			else
				(h::tail,po) 
	  |	
	  _ => (h::tail,po)

and

(* do *)
T(tokenlist)=
	let 
		val nextF=F(tokenlist)
		val nextTOne=T_one(#1nextF,#2nextF)
	in
		(#1nextTOne,#2nextTOne)
	end  

and

(* do *)
T_one(nil,a)=(nil,a)
|
T_one(h::tail,po)= case h of
	  OP(e) => if e="*" then
			let 
				val nextF=F(tail)	
				val operazione=MULT(po,#2nextF)
				val nextTOne=T_one(#1nextF,operazione)
			in
				nextTOne
			end
		   else
			if e="/" then
				let 
					val nextF=F(tail)	
					val operazione=DIV(po,#2nextF)
					val nextTOne=T_one(#1nextF,operazione)
				in
					nextTOne
				end
			else			
				(h::tail,po)
	  |  	
	  _ => (h::tail,po)

and 

(* do *)
Exp_const(NM(a)::c)= (c, NUM(a)) |
Exp_const(Nil::c)=(c, NIL) |
Exp_const(BOOL(a)::c)= (c, BOO(a)) |
Exp_const(STR(a)::c)= (c,STRI(a)) |
Exp_const(a)= raise NOCONST

and

(* do *)
F(h::tail)= 
let
	val costante=Exp_const(h::tail)
in
	(#1costante,#2costante)
end
handle NOCONST => let
			fun
			terminali(ID(x)::tail)= 
				let
					val y=Y(tail)				
				in
					if #2y=nil then
						(#1y,VAR(x))					
					else
						(#1y,CALL(VAR(x),#2y))
				end			
			|
			terminali(SYM(x)::tail)=
				(* x is the KEYWORD ( *)
				let
					val ea=ExpA(tail)
					(* hd(ea) is the KEYWORD ) *)			
				in
					(tl(#1ea),#2ea)			
				end
	          in
			terminali(h::tail)
		  end

and

(* do *)
Y(nil)=(nil,nil)
|
Y(h::tail) =
	    case h of
	    SYM("(") => let
				val seqExp=Seq_Exp(tail)
			in
				(* hd(tokenlist) is the KEYWORD ) *)
				(tl(#1seqExp),#2seqExp)
			end
	    |
	    _ => (h::tail,nil) 

and

(* do *)
Seq_Exp(nil)=(nil,nil)
|
(* se il primo elemento non è nel first di EXP torna la stessa lista passata *)
Seq_Exp(h::tail)= 
let fun nextExp(h::tail)= 
	case h of
	KEYWORD("let") => true
	|
	KEYWORD("letrec") => true	
	|	
	KEYWORD("lambda") => true
	|
	ID(a) => true
	|
	NM(a) => true
	|
	Nil => true
	|
	BOOL(a) => true
	|
	STR(a) => true 
	|
	SYM("(") => true			      	
	|
	OP("cons") => true
	|
	OP("car") => true
	|
	OP("cdr") => true
	|
	OP("eq") => true
	|
	OP("leq") => true
	|
	KEYWORD("if") => true
	|
	_ => false
	fun nextSym(SYM(",")::token)=true
	|
	nextSym(SYM(a)::token)=false
	(* scorriSeq assume che i terminali prodotti nel parametro passato (token) siano creati dal non terminale Exp *)
	fun scorriSeq(token)=
		let
			val exp=Exp(token)
			val nextToken = (#1exp)
		in
			if nextSym(nextToken) then
				(* hd(nextToken) è il SYM , *)
				#2exp::scorriSeq(tl(nextToken))
			else
				[#2exp]
		end
	(* scorriToken percorre i token fino a SYM ) escluso *)
	fun scorriToken(token)=
		let
			val exp=Exp(token)
			val nextToken= (#1exp)
		in
			if nextSym(nextToken) then
				(* hd(nextToken) è il SYM , *)
				scorriToken(tl(nextToken))
			else
				nextToken
		end
in
	if nextExp(h::tail) then
		let 
			val lista=scorriSeq(h::tail)
			val nextToken=scorriToken(h::tail) 
		in
			(nextToken,lista)
		end
	else
		(h::tail,nil)		
end

and

(* do *)
Seq_Var(x)=
let
	fun
	nextSym(SYM(")")::tail)=true
	|	  		
	nextSym(_)=false
	(* variabile permette di creare la lista di variabili *)
	fun variabili(tokens)=
		if not(nextSym(tokens)) then
			let
				val variabile=var(tokens)								
			in
				#2variabile::variabili(#1variabile)				
			end			
		else
			nil
	(* nextTokens scorre la lista di variabili e ritorna una lista di tokens la cui testa è la KEYWORD ) *)			       
	fun nextTokens(tokens)=if nextSym(tokens) then tokens else nextTokens(tl(tokens))
in			  	
	(nextTokens(x),variabili(x))
end

and

(* do *)
var(ID(a)::c)= (c,VAR(a)) 

and

(* do *)
Bind(h::tail)=
case h of
ID(variabile) => 
	let
		(* hd(tail) is the SEPARATOR = *)
		val nextExp=Exp(tl(tail))
		val nextX=X(#1nextExp)
			fun scorriX(token)=
				let
					val x=X(token)
				in
					if not(#2x=nil) then
						scorriX(#1x)
					else
						#1x
				end
		fun trad()= (VAR(variabile),#2nextExp) :: #2nextX			
	in
		(* nextExp e nextX contengono la parte della lista non ancora esaminata *)
		(scorriX(#1nextExp),trad())
	end	

and

(* do *)
X(nil)=(nil,nil)
|
X(h::tail) =
	   case h of
	   KEYWORD(a) => if a="and" then
				Bind(tail)
		         else
				(h::tail,nil)
	   |
	   _ => (h::tail,nil) 

and

(* do *)
esp_LAMB(c)= 
(* hd(c) is the separator ( *)
    let 
      val c1=Seq_Var(tl(c))
      (* hd(c1) is the separator ) *)
    in
      (tl(#1c1),#2c1)
    end

and

(* do *)
un_exp(c)=
(* hd(c) is the KEYWORD ( *)
    let 
      val c1 =Exp(tl(c))
      (* hd(c1) is the KEYWORD ) *)
    in
      (tl(#1c1),#2c1)
    end

and

(* do *)
due_exp(c)=
(* hd(c) is the KEYWORD ( *)
    let 
      val c1 =Exp(tl(c))
      (* hd(c1) is the SEPARATOR , *)
      val c2= Exp(tl(#1c1))
      (* hd(c2) is the KEYWORD ) *)
    in
	(tl(#1c2),#2c1,#2c2)
    end
in
 Prog
end;

exception SyntaxError;

(* crea_LKC prende in input una stringa *)
fun crea_LKC(programma: string)=
let
	val listaToken=PROG(lexi(explode(programma)))
	fun isSym(SYM("$")::everything)=true
	|
	isSym(everything)=false
in
	if isSym(listaToken) then
		PROG_LKC(lexi(explode(programma)))	
	else
		raise SyntaxError
end

val A="letrec  FACT = lambda ( X ) if  eq ( X, 0 ) then 1 else  X*FACT(  X - 1 )"^
"and G = lambda ( H L ) if  eq ( nil, L ) then L else cons( H(car( L ) ),"^ 
"G ( H, cdr ( L ) )) in G ( FACT, cons(1 ,cons(2, cons(3, nil))) ) end $";

val B= "let x= 5 and y= 6 in x * 3 + y * 2 * x + x * y end $";

val C="letrec PP = lambda ( x ) if eq ( x , 1) then 1 else"^
"  x * PP( x - 1 ) in  PP( 3 ) end $ ";

crea_LKC(A);
crea_LKC(B);
crea_LKC(C);

