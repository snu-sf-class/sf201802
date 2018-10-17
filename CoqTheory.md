# Term
- `Type`
- `forall (x:S), T`
- `Inductive D : forall (x1:S1),...,(xn:Sn),Type := ... | ci: forall (yi1:Si1),...,(yik:Sik), D ei1 ... ein | ...`
- `fix f (x:S) := e`
- `e1 e2`
- `ci`
- `match e as x in D x1 ... xn return T with ... | ci yi1 ... yik => ei | ... end`
  
# Evaluation rules
(Erefl)
```
==========
  e == e
```
(Etrans)
```
  e1 == e2   e2 == e3
=======================
  e1 == e3
```    
(Esym)
```
  e1 == e2
============
  e2 == e1
```
(Ealpha)
```
==================================================
  (fix f x := e) == (fix f' x' := e[f'/f][x'/x])
```
(Eeta)
```
  f, x not used in e
=========================
  e == (fix f x => e x)
```
(Eapp)
```
============================================================
  (fix f (x:S) := e) e1  ==  e[(fix f (x:S) := e)/f][e1/x] 
```
(Ematch)
```
========================================================================================
  match (ci ei1 .. eik) as x in D x1 ... xn return T with    
  ...
  | ci xi1 .. xik => ei                                    ==  ei[ei1/xi1]...[eik/xik]
  ...
  end  
```

# Typing rules
* Rules for `G Wf`

(Wemp)
```
=========
  () Wf
```
(Wvar)
```
  G Wf
  G |- T : Type
  x not in G
=================
  G, x:T Wf
```

* Rules for `G |- e : T`

(Tvar)
```
  G Wf
  x:T in G
============
  G |- x : T
```
(Teval)
```
  G Wf
  G |- e : S
  S == T
==============
  G |- e : T
```
(Ttype)
```
  G Wf
====================
  G |- Type : Type
```
(Tfun)
```
  G Wf
  G |- S : Type   
  G, x:S |- T: Type
=================================
  G |- forall (x:S),T : Type
```
(Tind)
```
  G Wf
  Inductive D : forall (x1:S1),...,(xn:Sn),Type := ... | ci: forall (yi1:Si1),...,(yik:Sik), D ei1 ... ein | ...
  G |- forall (x:S1),...,(x: Sn),Type : Type
  ...
  G, D:forall (x1:S1),...,(xn:Sn),Type |- forall (yi1:Si1),...,(yik:Sik), D ei1 ... ein : Type
  ...
=================================================================================================================
  G |- D : forall (x:S1),...,(x:Sn),Type
```
(Tfix)
```
  G Wf
  G |- forall (x:S),T : Type
  G, f:(forall (x:S),T), x:S |- e : T
=============================================
  G |- fix f (x:S) := e : forall (x:S),T
```
(Tapp)
```
  G Wf
  G |- e1 : forall (x: S),T
  G |- e2 : S
==============================
  G |- e1 e2 : T[e2/x]
```
(Tcon)
```
  G Wf
  Inductive D : forall (x1:S1),...,(xn:Sn),Type := ... | ci: forall (yi1:Si1),...,(yik:Sik), D ei1 ... ein | ...
  G |- D : forall (x:S1),...,(x:Sn),Type
=================================================================================================================
  G |- ci : forall (yi1:Si1),...,(yik:Sik), D ei1 ... ein
```
(Tmatch)
```
  G Wf
  Inductive D : forall (x1:S1),...,(xn:Sn),Type := ... | ci: forall (yi1:Si1),...,(yik:Sik), D ei1 ... ein | ...
  G |- D : forall (x:S1),...,(x:Sn),Type
  G |- e : D e1' ... en'
  G, x1:S1, ..., xn:Sn, x:D x1 ... xn |- T : Type
  ...
  G, yi1:Si1, ... , yik:Sik |- ei : T[ei1/x1,...,ein/xn,(ci yi1 ... yik)/x]
  ...
=================================================================================================================
  G |- match e as x in D x1 ... xn return T with ... | ci yi1 ... yik => ei | ... end : T[e1'/x1,...,en'/xn,e/x]
```
(Taxiom)
```
   G Wf
   G |- T : Type
   Axiom x : T
==================
   G |- x : T
```
