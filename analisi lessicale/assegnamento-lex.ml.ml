(* PROGETTO di LINGUAGGI 2013-14 Parte I ANALIZZATORE LESSICALE *)
(* la funzione I e' da fare   *)

datatype B = T | F ;

datatype token = KEYWORD of string  | OP of string | ID of string | SYM of string| NM of int | STR of string | BOOL of B| Nil ;

(*         Eccezioni      *)

exception NotValidChar of char;
exception UnexpectedEndOfString;
exception EmptyNumber;

(* fine Eccezioni *)

(* Analizzatore lessicale *)

(* Funzioni di supporto     *)
(* Testa se il carattere e' un carattere valido per iniziare
   un identificatore, un operatore o una keyword *)
fun IsAlphaChar(c: char) : bool =
  if (c >= (#"a") andalso c <=(#"z")) orelse (c>= (#"A") andalso c <= (#"Z")) 
      then true 
      else false;

(* riconosce se c e' un carattere numerico o no   *)
fun IsDigitChar(c)=
  if c>=(#"0") andalso c<= (#"9") 
  then
    true
  else
    false;

(* Testa se il carattere e' un carattere valido per comporre
   un identificatore, un operatore o una keyword (ad eccezione
   del primo carattere) *) 
fun IsIdChar(c: char) : bool =
  IsAlphaChar(c) orelse IsDigitChar(c);
  
(* Testa se il carattere e' un separatore *)
fun IsSeparator(c)=
  if  c= (#"(") orelse c=(#")") orelse c=(#"=") orelse c=(#"$") orelse c=(#",")
  then
    true
  else
    false;
(* testa se e' uno spazio o accapo *)

fun IsSpace(c)=
  if c=(#" ") orelse c=(#"\n") orelse c=(#"\f") orelse c=(#"\r") 
  then
    true
  else
    false;

fun IsOp(c)=
  if c=(#"+") orelse c=(#"-") orelse c=(#"*") orelse c=(#"/") 
  then
    true
  else
    false;
  

(* data una stringa X la confronta con le parole chiavi  e con gli operatori
del Lisp Kit e se e' una di queste cose, restituisce la corrispondente coppia
token_lexema, altrimenti la considera un identificatore e restituisce 
 la coppia (ID, STRINGA(X)) *)

fun extractWord("let": string) : token=
  KEYWORD("let") |
extractWord("in") =
  KEYWORD("in") |
extractWord("end") =
  KEYWORD("end") |
extractWord("letrec") =
  KEYWORD("letrec") |
extractWord("and") =
  KEYWORD("and") |
extractWord("nil") =
  Nil |
extractWord("true") =
  BOOL(T) |
extractWord("false") =
  BOOL(F) |
extractWord("eq") =
  OP("eq") |
extractWord("leq") =
  OP("leq") |
extractWord("car") =
  OP("car") |
extractWord("cdr") =
  OP("cdr") |
extractWord("cons") =
  OP("cons") |
extractWord("atom") =
  OP("atom") |
extractWord("if") =
  KEYWORD("if") |
extractWord("then") =
  KEYWORD("then") |
extractWord("else") =
  KEYWORD("else") |
extractWord("lambda") =
  KEYWORD("lambda") |
extractWord(s) =
  ID(s);
(* #endregion Funzioni di supporto *)

(* #Funzioni che implementano direttamente gli stati dell'automa. Osserva che non c'è ricorsione. Il passaggio dallo stato iniziale e principale I ad un altro stato è realizzato con un'invocazione. Poi si ritorna sempre a I e quindi basta il normale ritorno della funzione.
*)

(* Stato N per riconoscere i numeri *)

fun N(nil,n,b)= raise UnexpectedEndOfString |
N(c::l, n, b)=
  if IsDigitChar(c) 
  then
    let
val x= ord(c)-ord(#"0")
    in 
N(l,n*10+x,b)
      end
else
if b=true 
then (NM(~n),c::l)
else (NM(n),c::l);


(* Stato SC per riconoscere le stringhe tra virgolette    *)
fun SC(#"\""::l : char list, result : char list) : token*char list =
    (STR(implode(result)),l) |
SC(c::l, result) =
  SC(l, result@[c]) |
SC(nil, result) =
  raise UnexpectedEndOfString;
  

(* Stato S per raccogliere le stringhe che possono corrispondere
   ad identificatori, operatori prefissi o keyword *)
fun S(c::l: char list, result: char list) : token* char list=
  if IsIdChar(c) then
    S(l, result@[c])
  else 
    (extractWord(implode(result)),c::l)
|
S(nil, result) =
  raise UnexpectedEndOfString;
      

(*  FUNZIONE I DA FARE   *)

(* I implementa un automa che crea i token sintattici per il linguaggio  Lisp-kit *)
(* I si aspetta una stringa che termina con $ *)

fun I(nil)= raise UnexpectedEndOfString
|
I(h::tail)=
	let
		fun calcolotupla (tupla : token*char list) = #1tupla::I(#2tupla)
	in
	(* se incontro uno spazio rimango allo stato iniziale dell'automa ricorrendo sul prossimo carattere *)
	if IsSpace(h) then
		I(tail)
	else
		(* controllo se ho un numero negativo *)
		if h= #"~" then
			if IsDigitChar(hd(tail)) then		
				calcolotupla(N(tail,0,true))
				(* è stato trovato un token sintattico di tipo NM, torno allo stato iniziale dell'automa con il resto della lista *)
			else
				(* è stato trovato un carattere inaspettato, FINE dell'automa *)
				raise EmptyNumber
		else
			(* controllo se ho un numero positivo *)
			if IsDigitChar(h) then
				calcolotupla(N(h::tail,0,false))
				(* è stato trovato un token sintattico di tipo NM, torno allo stato iniziale dell'automa con il resto della lista *)
			else
				(* controllo se ho una stringa costante *)
				if h= #"\"" then
					calcolotupla(SC(tail,nil))
					(* è stato trovato un token sintattico di tipo SC, torno allo stato iniziale dell'automa con il resto della lista *)	
				else
					(* controllo se ho un operatore infisso, (operazioni aritmetiche) *)
					if IsOp(h) then
						OP(str(h))::I(tail)
					else
						(* controllo se ho un separatore *)
						if IsSeparator(h) then
							if h= #"$" then
								[SYM(str(h))]
							else	
								SYM(str(h))::I(tail)
						else
							(* controllo se ho un carattere che potrebbe rappresentare ID, OP *)
							if IsAlphaChar(h) then 
			         				calcolotupla(S(h::tail, nil))
							else
								raise NotValidChar (h)
	end;


(* #FINE delle  Funzioni che implementano l'automa a stati finiti *)

(* Funzione principale per l'analisi lessicale *)
fun lexi(s : char list) :  token list =
  I(s);

(* FUNZIONE DI TEST FUNZIONALE(BLACK BOX) *)
(* NegativeNumber viene lanciata se invoco la funzione test con num_ele negativo *)
(* ListaOverflow viene lanciata se invoco la funzione test con num_ele maggiore della dimensione della lista lisp_program *)
exception NegativeNumber;
exception ListaOverflow;

fun test(lisp_program: token list, tok_sintattico: string, num_ele: int)= 
case num_ele of
(0) =>	let
		fun getHead(h::tail, tok_sintattico)=
		let
			(* getType ricava il tipo della testa della lista tramite pattern matching, ritornando true se il tipo su cui effettua pattern è il tipo che ci si aspetta inglobato come stringa in tok_sintattico *)
			fun getType(KEYWORD(everything), tok_sintattico)= if tok_sintattico="KEYWORD" then true else false |
			getType(OP(everything), tok_sintattico)= if tok_sintattico="OP" then true else false |
			getType(ID(everything), tok_sintattico)= if tok_sintattico="ID" then true else false |
			getType(SYM(everything), tok_sintattico)= if tok_sintattico="SYM" then true else false |
			getType(NM(everything), tok_sintattico)= if tok_sintattico="NM" then true else false |
			getType(STR(everything), tok_sintattico)= if tok_sintattico="STR" then true else false |
			getType(BOOL(everything), tok_sintattico)= if tok_sintattico="BOOL" then true else false |
			getType(Nil, tok_sintattico)= if tok_sintattico="Nil" then true else false  	
		in
			getType(h, tok_sintattico)
		end
     	in
		(* getHead ottiene l'elemento in testa alla lista tramite pattern marching *)
		getHead(lisp_program, tok_sintattico)
     	end
|
(_) =>	if num_ele>0 then
		let
		fun scorri(h::tail)= tail |
		scorri(nil)=raise ListaOverflow
     		in
		(* scorro la lista fino ad arrivare all'elemento interessato *)
		test(scorri(lisp_program), tok_sintattico, (num_ele-1))
     		end
	else
		raise NegativeNumber;
	
	
(* #endregion Analizzatore lessicale *)


(* esempi di programmi in Lisp Kit per provare lexi *)

val C="letrec  FACT = lambda ( X ) if  eq ( X 0 ) then 1 else  X*FACT(  X- 1 )and G = lambda ( H L ) if  eq ( L  nil ) then L else cons( H(car( L ) ) G ( H cdr ( L ) )) in G ( FACT cons(1 cons(2 cons(3 nil))) ) end $";

val D= "let x=cons(\"ab\" cons(\"cd\" nil)) in if true then cons(\"01\" x) else nil end $";

(* tests *)
val listatokenC=lexi(explode(C));
val test0=test(listatokenC,"KEYWORD",0); (* l'elemento 0 dovrebbe essere di tipo KEYWORD *)
val test2=test(listatokenC,"SYM",2); (* l'elemento 2 dovrebbe essere di tipo SYM *)
val test4=test(listatokenC,"KEYWORD",4); (* l'elemento 4 dovrebbe essere di tipo SYM e non KEYWORD *)
val testecc=test(listatokenC,"KEYWORD",-1); (* dovrebbe lanciare un'eccezione *)

val listatokenD=lexi(explode(D));


