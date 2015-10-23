:- op(35,fx,'*=').
:- op(35,xfy,'*=').
:- op(65,fx,'*').
:- op(70,xfy,'?').
:- op(72,xfy,'*').
:- op(75,xfy,'#').
:- op(85,xfy,'@').
:- op(95,xfy,'<>').
builtin(findall(_X,_Y,_Z)).
builtin(quicksort(X,Y,Z)).
builtin(assert(_A)).
builtin(friend(_A)).
builtin(getfriend(_A,_B)).
builtin(bt_scan(_A)).
builtin(power(_A)).
builtin(check(_A)).
builtin(currentLocation(_A)).
builtin(findbound(_A,_B)).
builtin(showMap(_A,_B)).
builtin(mac(_A,_B)).
builtin(_A > _B).
builtin(_A \= _B).
builtin(_A @< _B).
builtin(_A is _B).
solve(true):-!.
solve(not(P)):- !,\+solve(P).
solve((P)):- builtin(P),!, P.
solve((P, Body)) :- !,solve(P), solve(Body).
solve((P)):-clause(P,Body),solve(Body).

solve((*=(A,B))):-!,solve(A),solve(B),crowdUni(A,B,all).
solve((A*=B)):- !,solve(A),solve(B),crowdUni(A,B,all).
solve((*=(A,B)@ST)):- !,solve(A),solve(B),crowdUni(A,B,ST).
solve((A*=B)@ST):- !,solve(A),solve(B),crowdUni(A,B,ST).
solve((A*=B)*PP#TT):- !,solve(A),solve(B),crowdUni(A,B,all,PP,TT).

crowdUni(Term1,Term2,ST):-    
    setLink(Term1,Term2,Path),
	setCond(Path,ST),asynproc(unify,Result).

crowdUni(Term1,Term2,ST,PP,TT):-
	setLink(Term1,Term2,Path),
	setCond(Path,ST,PP,TT),asynproc(unify,Result).

setLink(Term1,Term2,Path):- 
	Term1 =.. [Head1|Path1], Term2 =.. [Head2|Path2],
	length(Path1, Length1),length(Path2, Length2),
	(Length1 = 0,!,append(Path1,Head1,Link1); Path1 =.. [_H1|[Link1,T1]]),
	(Length2 = 0,!,append(Path2,Head2,Link2); Path2 =.. [_H1|[Link2,T2]]),
	Path = [Link1,Link2].

setCond(Path,ST):- 
	asserta(asktype('choice')),asserta(question('Are those pictures Yarra river?')),
    asserta(options(['Yes','No'])),asserta(picture(Path)),
    asserta(askto([bluetooth,mturk,facebook])),asserta(expiry('0,15,0')),asserta(supporttype(ST)).

setCond(Path,ST,PP,TT):-
	asserta(asktype('choice')),asserta(question('Are those pictures Yarra river?')),
    asserta(options(['Yes','No'])),asserta(picture(Path)),
	(TT = 2,!,asserta(expiry('0,2,0'));five(TT)),
    (PP = 'mix',!,asserta(askto([bluetooth,facebook,mturk]));mturk(PP)),
    asserta(supporttype(ST)).

five(TT) :- (TT = 5,!,asserta(expiry('0,5,0'));ten(TT)).
ten(TT) :- (TT = 10,!,asserta(expiry('0,10,0'));fifteen(TT)).
fifteen(TT):- (TT = 15,!,asserta(expiry('0,15,0'));one(TT)).
one(TT) :- (TT = 60,!,asserta(expiry('0,60,0'));two(TT)).
two(TT) :- (TT = 120,!,asserta(expiry('0,120,0'));three(TT)).
three(TT) :- (TT = 180,!,asserta(expiry('0,180,0'))).
mturk(PP) :- (PP = 'mturk',!,asserta(askto([mturk]));facebook(PP)).
facebook(PP):-(PP = 'facebook',!,asserta(askto([facebook]));bluetooth(PP)).
bluetooth(PP):-(PP = 'bluetooth',!,asserta(askto([bluetooth]))).

solve(PeerID*Askcrowd?Result#Condition):- !,
	solvecond(Condition),
	retract(askto(X)),
	solvepeer(PeerID),
    (asyn,!,asynproc(Askcrowd,Result); synproc(Askcrowd,Result)),
	doretraction.
solvepeer(PeerID):-  friend(PeerID,Mac), asserta(askto(Mac)).
solve(*Askcrowd?Result#Condition):- !,
	solvecond(Condition),
	asserta(forward(t)),
    (asyn,!,asynproc(Askcrowd,Result); synproc(Askcrowd,Result)),
	doretraction.

solve(Askcrowd?Result#Condition):- !,
	solvecond(Condition),
    (asyn,!,asynproc(Askcrowd,Result); synproc(Askcrowd,Result)),
	doretraction.
	
doretraction :-(asyn,!,retract(asyn);retract(syn)).

synproc(Askcrowd,Result):- 
	checkcond(TypeQuestion,Question,Namemsg,Link,Description,Picture,Options,Askto,Group,Locatedin,Expiry,EndTime,WPTime,Forward,ForwardQID,ST,AtLeast),
	askcrowd(syn,Askcrowd,TypeQuestion,Question,Options,Namemsg,Link,Description,Picture,Askto,Group,Locatedin,Expiry,EndTime,WPTime,Forward,ForwardQID,ST,AtLeast,QuestionID).
	registercallbacksyn(QuestionID,Question,Askto,TypeQuestion,Expiry,Forward,Result).

asynproc(Askcrowd,Result):- check(X),
	checkcond(TypeQuestion,Question,Namemsg,Link,Description,Picture,Options,Askto,Group,Locatedin,Expiry,EndTime,WPTime,Forward,ForwardQID,ST,AtLeast),
	askcrowd(asyn,Askcrowd,TypeQuestion,Question,Options,Namemsg,Link,Description,Picture,Askto,Group,Locatedin,Expiry,EndTime,WPTime,Forward,ForwardQID,ST,AtLeast,QuestionID),
	registercallbackasyn(Askcrowd,QuestionID,Question,Askto,TypeQuestion,Expiry,Forward,ST,AtLeast,Result),!.
	
solvecond([]):- !.
solvecond(Condition):- 
	Condition =..[_H|[Head,Body]],
	asserta(Head),
	solvecond(Body).

checkcond(TypeQuestion,Question,Namemsg,Link,Description,Picture,Options,Askto,Group,Locatedin,Expiry,EndTime,WPTime,Forward,ForwardQID,ST,AtLeast):- 
			(asktype(A),!, TypeQuestion = A; set(TypeQuestion)),
			(question(B),!, Question = B; set(Question)),
			(namemsg(C),!, Namemsg = C; set(Namemsg)),
			(link(D),!, Link = D; set(Link)),
			(description(E),!, Description = E; set(Description)),
			(picture(F),!, Picture = F; set(Picture)),
			(options(G),!, Options =G; set(Options)),
			(askto(H),!,Askto = H; set(Askto)),
			(group(I),!,Group = I; set(Group)),
			(locatedin(J),!,Locatedin = J; set(Locatedin)),
			(expiry(K),!,Expiry = K; set(Expiry)),
			(endtime(L),!,EndTime = L; set(EndTime)),
			(wptime(M),!,WPTime = M; set(WPTime)),
			(forward(N),!,Forward = N; set(Forward)),
			(forwardqid(O),!,ForwardQID = O; set(ForwardQID)),
			(supporttype(atleast(Value)),!,AtLeast=Value,ST = 'atleast';setsupport(AtLeast,ST)).

set(X):- X = 'null'.

setsupport(AtLeast,ST):- set(AtLeast),(supporttype(P),!,ST = P; set(ST)).

