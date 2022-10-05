NB. implement weigthed union-find
coclass 'unionfind'
NB. return union find structure (ufs)= dots and component size
create=: {{
  par =: i.  y  NB. parents
  sz  =: #&1 y  NB. compo size=# of children
}}

NB. find component number which y is part of (follow linked list) in ufs
find =: {{
  r=. par {~^:_ y NB. follow refs until done
  NB. important note: this is ok for root nodes, but sizes for non-root nodes will be off, and would neederebuilding.
  if. r~:y do. par=: r y}par end. NB. compress path
  r
  }}
NB. are x and y connected in x, i.e. in same component?
connected=: =&find
NB. join 2 components in y in usf x, balanced tree.
union2 =: {{
  comp=. find"_ 0 y
  if. =/comp do. par return. end.
  NB. append smaller to root of larger
  'a b'=. comp /: comp{sz NB. sort compo's per size
  NB. update smallest ref, largest size
  sz  =: (+/comp{sz) b}sz
  par =: b           a}par
}}
NB. add y new classes
add =: {{
  nn  =. #par         NB. current count
  par =. par,nn+ i.y NB. extend parent arr
  sz  =. sz, sz+1#~y NB. extend compo size
  }}
NB. do union with 2<#y later...
unionfind_z_=:conew&'unionfind'

NB. jegg - j egraphs great
NB. terms used:
NB. enode: operation applied to arguments 
NB. canonical enode: operation with canonical arguments
NB. canonical arg: where the arg is the root of the eclass i.e. find__uf y.
NB. eclass: equivalence class containing equivalent enodes, i.e. representing the same result
NB. eclassid: simply it's pos in the par/sz arrays

NB. egraph: set of enodes-edges->eclasses

NB. implementation details:
NB. - no classes for enodes/eclasses as this would hamper array implementation + performance.
NB. - jegg class represents egraph, keeps eclasses in unionfind
coclass 'jegg'
create=: {{
  NB. uf stores parents and class sizes (size correct for roots only, due to path compression)
  ecid   =: unionfind 0
  eciuses=: 0$a: NB. boxed 'uses' of each eclassid
  NB. i, version (for judging change) not needed?
  en   =: 0$a:  NB. enodes (str+canonical arg eclasses) stored
  ec   =: 0$0   NB. corresponding eclassid's
  enlu =: en&i. NB. lookup function
  work =: 0$0   NB. eclass id's to be processed
}}
NB. canonicalize enode: self with canonic (root) reps of args
NB. any reason not to have enodes all be canonical?
NB. handle in array fashion; canonicalise all at once

arofu=: 1 : '5!:1<''u'''
NB. go through AR, encoding enodes on the go
NB. AR summary: boxed string if prim / named verb
NB. if not: box with 2 boxes
NB. first: string (number char list or conj)
NB. 0 : noun
NB. 2 : hook
NB. 3 : fork
NB. 4 : modifier train (N/A for the moment)
NB. applied adv/conj, followed by list of args (N/V)
NB. add_enode+add_node: y: string rep (for now) of fun to be added
NB. add enode y= (ar);(arg classes) TODO or better str instead of ar? arg classes is one box with N args
adden =: {{
  NB. canonicalise y to get enode
  newen =. ({. , find__ecid each@}.) y
  if. (#en)<eciInd=.enlu newen do.
    NB. inc version if needed
    eciInd =. add__ecid 1
    NB. update eciuses for relevant eclassids
    eciuses =. eciuses (>{:newen)}~ newen ,<eciInd
    NB. update en,ec and enlu
    en=. en,newen
    ec=. ec,eciInd
    enlu=. en&i.
  end.
  find__ecid ec{~eciInd
}}
NB. addxxx  : add different parts of speech, y=AR, awgmented with outer layer of arguments x::,y::,u::,v::,m::,n::
NB.  each recursively descends through AR
NB. add: dyad: recursively add enodes
NB. x: type adv/conj/monad/dyad = 1 to 4
NB. y: AR to add
add =: {{
  NB. TODO: could probably be more robust; actually only monad/dyad needs disambiguation.
  NB. pre-create args for type& add already
  args =. 2 2$;:'v::u::x::y::'
  NB. |.^:(x=2) because adv take  
  at =. ([: adden '';~]) each |.^:(x=2) (-1+-.2|x){. args{~ x>1
    select. {.y
    case. ,'0' do. NB. noun
    case. ,'2' do. NB. hook
    case. ,'3' do. NB. fork
    case. ,'4' do. NB. modifier train
    case. do. NB. applied adv/conj
NB. addmonad:
addmonad=: {{
  y=. >y
  NB. primitive or named add with placeholder arg
  if. 0=L. y do. adden y, adden 'y::';'' else.
    NB. not primitive: recurse through AR
  end.
}}

NB. adddyad:
NB. addadv:
NB. addconj:
NB. addnoun:
