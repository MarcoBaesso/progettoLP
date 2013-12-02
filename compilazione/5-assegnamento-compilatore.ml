(* Compilatore LKC --> SECD incompleto Novembre 2012  *)

datatype secdexpr = Add | 
                    Ap | 
                    Atom | 
                    Car | 
                    Cdr | 
                    Cons | 
                    Div | 
                    Eq | 
                    Join | 
                    Ldc of LKC|
                    Ldf of  secdexpr list |
                    Ld of int*int |
                    Leq | 
                    Mult | 
                    Rap | 
                    Rem | 
                    Rtn | 
                    Sel of secdexpr list * secdexpr list|
                    Stop | 
                    Sub |  
                    Var of string;
(* funzioni per il calcolo dell'indirizzo di una variabile nell'ambiente ******)
fun position (x:string, a: LKC list):int =
    (* calcola la posizione di un elemento all' interno di una lista; 
     * il suo offset *)
   let val VAR (w) = hd (a) in 
      if x = w then 
         0 
      else 
         1+position (x,tl (a)) 
   end;
fun member (x:string, l:LKC list) =
    (* ritorna TRUE se l'elemento x 'e contenuto nella lista l *)
   if l=[] then 
      false 
   else 
      let val VAR (w) = hd (l) in 
         if x=w then 
            true 
         else 
            member (x,tl (l)) 
      end;
fun location (x:string, ct:int, n:LKC list list): int*int =
(* il risultato dell' invocazione sarà una coppia di interi (int * int)
 * (n1,n2)
 * n1 individua la n1-esima lista dell ambiente E (la sua copia a compile-time
 * si chiama n) 
 *     (n1=0 lista in cima a E, n1=1 la seconda in cima) 
 * n2 identifica l' n2-esimo valore della n1-esima lista *)
   if member (x,hd (n)) then 
      (ct,position (x,hd (n))) 
   else
      location (x,ct+1,tl (n)); 
fun sexpr_reverse (l)=
   if l = [] then 
      [] 
   else 
      sexpr_reverse (tl (l))@[hd (l)];
(* selezionare tutte le parti sinistre e tutte le parti destre (vars/exprs) 
 *  da una lista di Binders ***********************)
fun vars (nil)= [] |
   vars ((x,y)::R) = x :: vars (R);
fun exprs (nil)= [] |
   exprs ((x,y)::R) = y:: exprs (R);
   
(* complist prepara (in cima alla pila S) la lista dei PARAMETRI ATTUALI di: 
 * un'invocazione di funzione 
 * o dei valori dei binders di un LET/LETREC *) 
fun complist (nil: LKC list,n: (LKC list) list,c: secdexpr list):secdexpr list = 
    (* #1 lista di parametri attuali
     * #2 ambiente statico; il cui il significato delle liste che la compongono
     *    'e esattamente lo stesso che in E (ambiente dinamico)
     * #3 il codice SECD prodotto fino a quel istante *) 
      (Ldc NIL)::c |
      (* Carica sulla pila S la constante NIL (tipo LKC)
       * ritorna anche c (il codice SECD prodotto fino a quel istante)*)
   complist (x::y: LKC list,n: (LKC list)list,c: secdexpr list): secdexpr list =
             complist (y,n,
             (* prepara la lista dei Parametri Attuali y; 
              * le lascia in cima alla S *)
               COMP (x,n,Cons::c)
               (* Traduce il programma LKC x:
                * -una invocazione di funzione 
                * -o dei valori dei binders di LET/LETREC
                * il codice prodotto fino a quel istante lo lascia in c *)
             )
and
   COMP(e:LKC, n: (LKC list) list, c: secdexpr list): secdexpr list=
   (* Produce il significato di ogni espressione 'e' 
    * (quindi dei programi LispKit), il significato di 'e' 'e il programa SECD
    * COMP(e,[],[]);
    * Il significato di 'e' 'e  il risultato che si ottiene eseguendo 
    * COMP(e,[],[]) sulla macchina SECD 
    * #1 il programma LKC per tradurre
    * #2 l'ambiente  statico
    * #3 il codice SECD prodotto fino a quel istante
    * #return il risultato della traduzione *)
      case e of 
         VAR (x) => Ld (location (x,0,n))::c |
         (* la funzione 'location': 
          * calcola l'indirizzo (n1,n2) della variabile x in n
          * l'istruzione Ld (n1,n2), nella macchina SECD
          * ha il compito di caricare sullo S il R-valore della variabile x *)
         NUM (x) => Ldc (NUM (x))::c | 
         BOO (x) => Ldc (BOO (x))::c  |
         STRI (x) => Ldc (STRI (x))::c |
         NIL => Ldc (NIL)::c |
         ADD (x,y) => COMP (y,n,COMP (x,n,Add::c))| 
         (* carica sullo stack S il valore di y COMP(y,n_)
          * poi carica il valore di x 
          * e poi ne fa la somma eseguendo l'operatore Add *)
         SUB (x,y) => COMP (y,n,COMP (x,n,Sub::c))|
         MULT (x,y) => COMP (y,n,COMP (x,n,Mult::c))|
         DIV (x,y) => COMP (y,n,COMP (x,n,Div::c))|
  (*       REM (x,y) => COMP (y,n,COMP (x,n,Rem::c))|  da errore al compilare *)
         EQ (x,y) => COMP (y,n,COMP (x,n,Eq::c))|
         LEQ (x,y) => COMP (y,n,COMP (x,n,Leq::c))|       
         CAR (x) => COMP (x,n, Car::c) | 
         CDR (x) => COMP (x,n, Cdr::c) | 
         CONS (x,y) => COMP (y, n, COMP (x,n, Cons::c)) | 
         ATOM (x) => COMP (x,n, Atom::c) |        
         IF (x,y,z) => 
         (* Carica sullo stack S il valore di x
          * dopo viene eseguito Sel(thenp, elsep);
          * esegue thenp oppure elsep aseconda di x
          * Il calcolo continua; cio'e dal programma z previamente salvato su D
          * #1 condizione del condizionale
          * #2 thenp
          * #3 elsep
          *)
            let 
               val thenp = COMP (y,n,[Join]) 
               and  elsep = COMP (z,n,[Join]) 
            in
               COMP (x,n, Sel (thenp,elsep)::c) 
            end |
         LAMBDA (parform,body) => 
         (* Produce il codice SECD corrispondente al corpo body
          * usando un ambiente statico n, a cui viene aggiunta all'inizio la
          * lista di parametri formali della funzione
          * #1 parametri formali
          * #2 corpo della funzione *)
            Ldf (
            (* costruisce in cima alla pila S la chiusura della funziona che
             * 'e definita*)
               COMP (body,parform::n,[Rtn])
               (* Produce il significato di 'e' -> il prog SECD COMP(e,[],[]) 
                * COMP (
                 * e:=body,
                * AmbienteStatico:=parform::n,
                * ilCodiceProdottoFinoAdesso:= [Rtn]) *)
            )::c |
            (* c: 'e il codice SECD prodotto fino a quel istante*) 
         LET (body,binders) =>
         (* &&& 'e la unione di CALL e LAMBDA
          * -Una LET produce Binders 'x=exp' in cui le variabili x, per il corpo
          * del LET; sono tutto simili ai parametri formali del caso LAMBDA.
          * -Il corpo del LET va compilado mettendo queste variabili locali in 
          * cima all'ambiente statico n usato dal compilatore
          * -Per altra parte, i valori delle variabili locali (cio'e i valori
          * dei exp) hanno lo stesso ruolo di parametri attuali di una CALL
          * quindi in correspondenza a questi valori i comenti &&& *)
            let
            (* binders ha una lista di Bind del tipo 'x=exp' 
             * Quindi si dividono gli x, dai valori exp *)
               val var_list = vars (binders); 
               (* L-value (x) *)
               val exp_list = exprs (binders); 
               (* R-value (exp) *)
            in
               complist (exp_list,n, [
               (* &&& va prodotto codice SECD che costruisca una lista di questi 
                * valori sullo Stack S &&& *)
               (* prepara (in cima alla pila S) la lista dei PARAMETRI ATTUALI 
                * dei valori dei binders; i R-value (exp) 
                * che serviranno poi nel corpo della LET *)
                  Ldf (
                  (* genera una istruzione SECD che dopo si convertira 
                   * nella chiusura dall' interprete *)
                     COMP (body, var_list::n, [Rtn])
                     (* Produce il significato di 'e' -> il programma SECD 
                      * COMP(e,[],[]) : 
                      * COMP (
                      * e:=body,
                      * AmbienteStatico:=var_list::n, : gli L-value (x)
                      * ilCodiceProdottoFinoAdesso:= [Rtn]) *)
                  )
                  (* &&& sopra questa lista viene inserita la chiusura del corpo
                   * del LET &&& *)
               ]@[
                  Ap
                  (* &&& Far'a eseguire il corpo del LET nell'ambiente dinamico
                   * corretto; con i valori delle variabili locali disponibili
                   * ed al posto giusto, cio'e, in cima all'ambiente dinamico 
                   * &&& *)
               ]@c)
               (* c: 'e il codice SECD prodotto fino a quel istante*) 
            end|         
         LETREC (body,binders) =>
         (* &&& 'e molto simile a LET, una differenza 'e che usa Rap invece di
          * Ap 
          * Si deve fare atenzione che la traduzione dei Binders sia effetuata
          * in un ambiente Statico che contenga le variabili locali dei Binders
          * del LETREC (cio'e le parti sinistre dei Binders). Questo perch'e 
          * quando le funzioni ricorsive, definite nelle parti destre dei 
          * binders, verrano eseguite, questo averr;a in un Ambiente Dinamico 
          * che conterr'a le Chiusure delle funzione stesse. 
          * Solo cosi si potrano eseguire le invocazioni ricorsive; questo 
          * effeto viene ottenuto costruendo delle Chiusure Circolari per le
          * funzioni ricorsive definite nei binders di LETREC
          * Cio'e Chiusure che nella seconda componente (ambiente di definizione
          * della funzione) contengono la chiusura stessa.
          * Le Chiusure Circolari vengono realizzati da Rap &&& *) 
         (* in una funzione ricorsiva la parte ricorsiva non 'e il body
          * 'e il binder *)
            let
            (* binders ha una lista di Bind del tipo 'x=exp' 
             * Quindi si dividono gli x, dai valori exp *)
               val var_list = vars (binders); 
               (* L-value (x) *)
               val exp_list = exprs (binders); 
               (* R-value (exp) *)
            in
               complist (exp_list,var_list::n,[
               (* &&& va prodotto codice SECD che costruisca una lista di questi 
                * valori sullo Stack S &&& *)
               (* prepara (in cima alla pila S) la lista dei PARAMETRI ATTUALI 
                * dei valori dei binders; R-value (exp) 
                * che serviranno poi nel corpo della LETREC 
                * Noti che  al ambiente statico n viene aggiunto i var_list *)
                  Ldf (
                  (* genera una istruzione SECD che dopo si convertira 
                   * nella chiusura dall' interprete *)
                     COMP (body,var_list::n,[Rtn])
                     (* Produce il significato di 'e' -> il programma SECD 
                      * COMP(e,[],[]) : 
                      * COMP (
                      * e:=body,
                      * AmbienteStatico:=var_list::n, : gli L-value (x)
                      * ilCodiceProdottoFinoAdesso:= [Rtn]) *)
                  )
                  (* &&& sopra questa lista viene inserita la chiusura del corpo
                   * del LET &&& *)
               ]@[
                  Rap
                  (* crea l'ambiente dinamico ricorsivo (le chiusure Circolari; 
                   * cio'e chiusure che nella seconda componente [ambiente di 
                   * definizione della funzione] contengono la chiusura stessa),
                   * necessario per il trattamento della ricorsione
                   * Fa eseguire il corpo del LETREC nell'ambiente dinamico  *)
                   (* &&& Fa eseguire il corpo del LETREC nell'ambiente dinamico
                   * corretto &&& *)
               ]@c)
               (* c: 'e il codice SECD prodotto fino a quel istante*)
            end|         
         CALL (paratt,nome) => 
         (* Costruisce sullo stack S la lista di parametri attuali
          * la traduzione del nome sar'a semplicemente Ld(n1,n2) 
          * dove (n1, n2): 'e la posizione nell'ambiente dinamico E
          * della chiusura che 'e il valore della funzione invocata*)
            complist (nome,n,
            (* prepara (in cima alla pila S) la lista dei PARAMETRI ATTUALI di 
             * un'invocazione di funzione *)
             (* #1 listaParamAttuali:= nome
              * #2 ambienteStatico; il cui il significato delle liste che la 
              *    compongono 'e esattamente lo stesso che in E 
              *    (ambiente dinamico)
              * #3 il codice SECD prodotto fino a quel istante *) 
               COMP (paratt,n,Ap::c)
               (* Produce il significato di 'e' -> il programma SECD 
                * COMP(e,[],[]) : 
                * e:=paratt, : parametriAttuali
                * AmbienteStatico:=n,   
                * ilCodiceProdottoFinoAdesso:= Ap::c 'e il codice SECD prodotto
                *                              fino adesso *)
               
            ); 
(* esempi di prova 
val C = "letrec  FACT = lambda ( X ) if  eq ( X, 0 ) then 1 else  X*FACT(  X "^
"- 1 ) and G = lambda ( H L ) if  eq ( nil, L ) then L else cons( H(car( L ) )"^ 
",G ( H, cdr ( L ) )) in G ( FACT, cons(1 ,cons(2, cons(3, nil))) ) end $";
val S= "let x= 5 and y= 6 in x*3 + y * 2* x + x*y end $";
val D= lexi(explode(C));
val q=(PROG(D)); 
COMP(#1q,[],[]);
*)
val S = "let sum = lambda(x y) x+y in sum(4 , 5) + 2 end $";
val codice_tocompile=crea_LKC(S); 
val codice_compilato=COMP(#2codice_tocompile,[],[]);
