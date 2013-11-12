(* PARSER LispKit  incompleto Novembre 2012*)

(* richiamare l'analizzatore lessicale *)

(*         Eccezioni      *)

exception NOCONST;
exception Etwo of string*string;
exception ex of string;
(* fine Eccezioni *)


(* funzioni per DEBUG ***************************)

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

(*  AUSILIARIA *****************************)
fun trova_stringa(nil,x)=
  raise ex("la stringa termina prematuramente") |
  trova_stringa(KEYWORD(a)::z,x)= a=x |
  trova_stringa(OP(a)::z,x)= a=x |
  trova_stringa(ID(a)::z,x)= a=x |
  trova_stringa(SYM(a)::z,x)= a=x |
  trova_stringa(STR(a)::z,x)= a=x|
  trova_stringa(_,_)= false;

(* Analizzatore sintattico ****************************)
(* usare la let forma una specie di namespace evitando involontari conflitti di nome tra le funzioni definite
nelle diverse parti del programma *)

val PROG= let

fun 
Prog (nil): token list =
  raise ex("Prog: terminazione imprevista")|
Prog(KEYWORD(a)::c)=
    if not(a="let" orelse a="letrec")
    then 
      raise ex("Prog: programma inizia senza let/letrec")
    else 
      let 
      val x1=Bind(c)
      fun nextKey(KEYWORD("in")::tail)=true|		
	nextKey(_)=false 
      in
      if not(nextKey(x1)) 
          then raise Etwo("Prog: no in dopo bind",g(x1))
      else 
	  let 
	  val x2=Exp(tl(x1))
	  fun
		nextKey(KEYWORD("end")::tail)=true
		|		
		nextKey(_)=false 
          in
	  if not(nextKey(x2))
          then 
	   raise Etwo("Prog: no end alla fine del programma", g(x2) )
          else 
	   tl(x2)
	  end                    
      end
|
Prog(_)= raise ex("Prog: programma inizia senza keyword")
  
and

Exp(nil)= raise ex("Exp: input termina prematuramente")
|
Exp(KEYWORD("let")::c)= Prog(KEYWORD("let")::c)
|
Exp(KEYWORD("letrec")::c)= Prog(KEYWORD("letrec")::c)
|
Exp(KEYWORD("lambda")::c)= Exp(esp_LAMB(c)) 
|
Exp(OP("cons")::c) = due_exp(c)
|     
Exp(OP("car")::c) = un_exp(c)
|     
Exp(OP("cdr")::c) = un_exp(c) 
|     
Exp(OP("eq")::c) = due_exp(c)
|     
Exp(OP("leq")::c) = due_exp(c)
|     
Exp(OP("atom")::c) = un_exp(c)
|     
Exp(KEYWORD("if")::c) = 
  let 
    val x1=Exp(c)
    fun
	nextKey(KEYWORD("then")::tail)=true
	|
	nextKey(_)=false
  in
  if not(nextKey(x1))
  then
    raise Etwo("Exp: dopo if exp niente then",g(x1))
  else
    let 
    val x2=Exp(tl(x1))
    fun
	nextKey(KEYWORD("else")::tail)=true
	|
	nextKey(_)=false
    in
    if not(nextKey(x2))
    then 
      raise Etwo("Exp: dopo if_then niente else",g(x2))
    else
	Exp(tl(x2))
    end
  end
| (* espressioni aritmetiche *)  
Exp(x)= ExpA(x) (*5 ExpA::= T E1 *)

and

(* add by me*)
ExpA(nil)= raise ex("ExpA: terminazione inaspettata, ci si aspettava un ID, una costante o un simbolo di )")
|
ExpA(tokenlist)=
	let 
		val nextT=T(tokenlist)
		val nextEOne=E_one(nextT)
	in
		nextEOne
	end  

and 

(* add by me*)
E_one(nil)=nil
|
E_one(h::tail)=case h of
	  OP(e) => if e="+" orelse e="-" then
			let 
				val nextT=T(tail)
				val nextEOne=E_one(nextT)
			in
				nextEOne
			end
		     else
			h::tail 
	  |	
	  _ => h::tail

and

(* add by me*)
T(nil)= raise ex("T: terminazione inaspettata, ci si aspettava un ID, una costante o un simbolo di aperta parentesi")
|
T(tokenlist)=
	let 
		val nextF=F(tokenlist)
		val nextTOne=T_one(nextF)
	in
		nextTOne
	end  

and

(* add by me *)
T_one(nil)=nil
|
T_one(h::tail)= case h of
	  OP(e) => if e="*" orelse e="/" then
			let 
				val nextF=F(tail)
				val nextTOne=T_one(nextF)
			in
				nextTOne
			end
		   else
			h::tail
	  |  	
	  _ => h::tail

and 

Exp_const(nil):token list= 
raise ex("Exp_const: input termina prematuramente")|
Exp_const(NM(a)::c:token list)= c |
Exp_const(Nil::c)=c |
Exp_const(BOOL(a)::c)= c |
Exp_const(STR(a)::c)= c |
Exp_const(a)= raise NOCONST

and

(* add by me, gestita eccezione NOCONST *)
F(nil)=raise ex("F: input termina prematuramente")
|
F(h::tail)= Exp_const(h::tail)
handle NOCONST => let
			fun
			terminali(ID(x)::tail)= Y(tail)			
			|
			terminali(SYM(x)::tail)=
				if x="(" then
				let
					val ea=ExpA(tail)
					fun nextSYM(SYM(x)::tail)= x=")"
					|
					nextSYM(sometoken)=raise ex("F: ) mancante")				
					fun nextTokens()=if nextSYM(ea) then tl(ea) else raise ex("F: ) mancante")
				in
					nextTokens()			
				end
				else
					raise ex("F: terminali necessari non trovati "^g(h::tail))
			|
			terminali(something)=raise ex("F: terminali necessari non inseriti")
	          in
			terminali(h::tail)
		  end

and

(* add by me *)
Y(nil)=nil
|
Y(h::tail) =
	    case h of
	    SYM("(") => let
				val tokenlist=Seq_Exp(tail)
				fun nextSYM(nil)=raise ex("Y: inspettata terminazione del programma")
				|
				nextSYM(h::tail)=case h of
						SYM(")") => tail	
						|
						_ => raise ex("Y: ) mancante")
			in
				nextSYM(tokenlist)
			end
	    |
	    _ => h::tail 

and

(* add by me *)
Seq_Exp(nil)=nil
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
in
	if nextExp(h::tail) then
		Sep(Exp(h::tail))
	else
		h::tail		
end

and

(* add by me, il terminale aggiunto *)
Sep(nil)=nil
|
Sep(h::tail) = case h of
		SYM(",") => Seq_Exp(tail)
		|
	       	_ => h::tail

and

Seq_Var(nil):token list=
raise ex("Seq_Var: la stringa termina prematuramente")|
 Seq_Var(x)= let
		fun
			nextSym(SYM(")")::tail)=true
			|	  		
			nextSym(_)=false
	     in
		if not(nextSym(x)) then
		  Seq_Var(var(x))
		else
 		 x (* non consumo la ) che va consumata in Exp *)
             end

and

var(nil):token list =
raise ex("var: la stringa termina prematuramente")|
var(ID(a)::c)= c 
|
var(x)= raise ex("var: oggetto estraneo in Var_List "^g(x))

(*2 Bind::= var = Exp X 3 X::= and Bind | epsilon *)

and

(* add by me *)
Bind(nil)= raise ex("Bind: la stringa termina prematuramente")
|
Bind(h::tail)=
case h of
ID(_) => 
	let
		fun 
		nextSym(nil) = raise ex("Bind: inaspettata terminazione, necessario effettuare un'assegnazione")
		|		
		nextSym(s::tail) = 
		case s of
		SYM("=") => tail
		| 
		_ => raise ex("Bind: non è stato trovato simbolo di uguaglianza dopo l'inserimento di un ID all'interno di let letrec")
		val nextExp=Exp(nextSym(tail))
		val nextX=X(nextExp)			
	in
		(* nextExp e nextX contengono la parte della lista non ancora esaminata *)
		nextX
	end
|
_ => raise ex("Bind: non trovato ID")		

and

(* add by me *)
X(nil)=nil
|
X(h::tail) =
	   case h of
	   KEYWORD(a) => if a="and" then
				Bind(tail)
		         else
				h::tail
	   |
	   _ => h::tail 

and

(* serve per riconoscere la sequenza di parametri formali di una lambda *)
esp_LAMB(c)= 
let
      fun 
	nextSym(SYM("(")::tail)=true
	|
  	nextSym(_)=false
in
  if not(nextSym(c))
  then 
    raise ex("esp_LAMB: manca chiusa parentesi")
  else 
    let 
      val c1=Seq_Var(tl(c))
      fun
	nextSym(SYM(")")::tail)=true
	|
	nextSym(_)=false 
    in
    if nextSym(c1)
      then 
	tl(c1)
      else
      raise ex("esp_LAMB: ) mancante")
    end
end

and

(* add by me*)
un_exp(nil)=raise ex("un_exp: ( mancante")
|
un_exp(c)=
let
      fun 
	nextSym(SYM("(")::tail)=true
	|
	nextSym(_)=false 
in
  if not(nextSym(c))
  then 
    raise ex("un_exp: la stringa termina prematuramente senza il terminale )")
  else 
    let 
      val c1 =Exp(tl(c))
      fun 
	nextSym(SYM(")")::tail)=true
	|	  
	nextSym(_)=false  
    in
	if nextSym(c1) then
		tl(c1)
	else
	    raise ex("un_exp: la stringa termina prematuramente senza il terminale (")	
    end
end

and

due_exp(c):token list=
let
      fun
	nextSym(SYM("(")::tail)=true
	|
	nextSym(_)=false 
in
  if not(nextSym(c))
  then 
    raise ex("due_exp: la stringa termina prematuramente")
  else 
    let 
      val c1 =Exp(tl(c))
      fun
	nextSym(SYM(",")::tail)=true
	|	
	nextSym(_)=false  
    in
    if nextSym(c1) then
      let
        val c2= Exp(tl(c1))
	fun
		nextSym(SYM(")")::tail)=true
		|		
		nextSym(_)=false 
      in
        if nextSym(c2)
          then 
            tl(c2)
          else
            raise ex("due_exp: ) mancante")
       end
     else
       raise Etwo("non c'è , tra 2 expr",g(c1)) 
    end
end

in
 Prog
end;

val A="letrec  FACT = lambda ( X ) if  eq ( X, 0 ) then 1 else  X*FACT(  X - 1 )"^
"and G = lambda ( H L ) if  eq ( nil, L ) then L else cons( H(car( L ) ),"^ 
"G ( H, cdr ( L ) )) in G ( FACT, cons(1 ,cons(2, cons(3, nil))) ) end $";

PROG(lexi(explode(A)));

val B= "let x= 5 and y= 6 in x * 3 + y * 2 * x + x * y end $";

PROG(lexi(explode(B)));

val C="letrec PP = lambda ( x ) if eq ( x , 1) then 1 else"^
"  x * PP( x - 1 ) in  PP( 3 ) end $ ";

PROG(lexi(explode(C)));

