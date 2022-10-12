NB. Weighted-tree unionfind with path compression
NB. ========================================
coclass 'unionfind'
NB. return union find structure (ufs)= dots and component size
create=: {{
  par =: i.  y  NB. parents
  siz =: #&1 y  NB. compo size=# of children
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
union =: {{
  comp=. find"_ 0 y
  if. =/comp do. par return. end.
  NB. append smaller to root of larger
  'a b'=. comp /: comp{siz NB. sort compo's per size
  NB. update smallest ref, largest size
  siz =: (+/comp{sz) b}siz
  par =: b           a}par
}}
NB. add y new classes
add =: {{
  nn  =. #par        NB. current count
  par =: par,r=.nn+ i.y NB. extend parent arr
  siz =: siz,   1#~y NB. extend compo size
  r NB. return added indices
  }}
NB. do union with 2<#y later...
unionfind_z_=:conew&'unionfind'

NB. jsym - j's version of egraphs great
NB. ========================================
NB. terms used:
NB. enode: operation applied to arguments 
NB. canonical enode: operation with canonical arguments
NB. canonical arg: where the arg is the root of the eclass i.e. find__uf y.
NB. eclass: equivalence class containing equivalent enodes, i.e. representing the same result
NB. eclassid: simply it's pos in the par/sz arrays

NB. egraph: set of enodes-edges(args)->eclasses
NB. sym term: terms meaningless to J, but used for jsym like x::, y:: for arguments of verbs, and u:: v:: for arguments of operators. Likely extended in the future by e.g. deriv::, pderiv::, ...

NB. implementation details:
NB. - no classes for enodes/eclasses as this would hamper array implementation + performance.
NB. - jegg class represents egraph, keeps eclasses in unionfind
NB. - based partially on https://colab.research.google.com/drive/1tNOQijJqe5tw-Pk9iqd6HHb2abC5aRid?usp=sharing
coclass 'jsym'
NB. PRIMADV=:;:'~//./..\\.]:}b.f.M.'
NB. PRIMCON=:;:'^: . : :. :: ;.!.!:[.]."` @ @. @:&&.&:&.:F.F..F.:F:F:.F::H.L:S:t.'
create=: {{
  NB. uf stores parents and class sizes (size correct for roots only, due to path compression)
  ecid   =: unionfind 0
  eciuses=: 0$a: NB. boxed 'uses' of each eclassid (enode,
  NB. i, version (for judging change) not needed?
  en   =: 0 2$a:  NB. enodes (str+canonical arg eclasses) stored
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

NB. add enode y= (ar);(arg classes) , or a bare string, which should contain 'leaf' argument (i.e. a primitive; or symterm like x:: or y::)
NB. TODO or better str instead of ar? arg classes is one box with N args
adden =: {{
  yy =. 2 {. boxopen y NB. TODO: assertions needed?
  NB. canonicalise y to get enode
  newen =. ({. , find__ecid each@}.) yy
  if. (#en)=eciInd=.enlu newen do. NB. new enode not known yet
    NB. inc version if needed
    eciInd =. {. add__ecid 1    NB. create new eclass id
    eciuses =: eciuses ,<0 3$a: NB. add entry for self.
    NB. update eciuses for relevant eclassids of arguments of newen.
    eciuses =: eciuses (>{:newen)}~ (eciuses{~>{:newen) ,&.> <newen,<eciInd
    NB. update en,ec and enlu, to include new enode, corresponding enode class, and update lookup function.
    en=: en,newen
    ec=: ec,eciInd
    enlu=: en&i.
  end.
  find__ecid ec{~eciInd
}}
NB. add : add different parts of speech, y=AR,<list of args. 
NB.  each recursively descends through AR
NB. add: dyad: recursively add enodes
NB. x: type adv/conj/monad/dyad = 1 to 4
NB. y: AR to add
add =: {{
  'op args' =. 2{.boxopen y NB. discard outer box.
  NB. TODO: could probably be more robust; actually only monad/dyad needs disambiguation.
  NB. if arguments are boxed, internalise them
  if. *L.args do.
    args  =. ([: adden '';~])&> args
  end.

  NB. Literal: prim (also adv/conj!) or named verb 
  if. 0=L. op do.
    NB. add verb as leaf. application on args done by RW rules.
    adden op;args 
    return.
  end.
  NB. Others: recurse through tree, top down
  select. >{.op
    case. ,'0' do. NB. noun directly call adden.
      adden <op return.   NB. takes no args; needs box to keep adden to interpret values as arguments.
    case. ,'2' do. NB. hook
      add 'h::';add&>{:op
    case. ,'3' do. NB. fork
      add 'f::';add&>{:op
    case. ,'4' do. NB. modifier train
      'mod train nyi' assert 0
    case. do. NB. applied adv (1 arg)/conj (2 args)
      add (>{.op);add&>>{:op
  end.
}}

NB. apply verb to args: x 3 or 4 for monad/dyad, y AR of verb. if x not given; >{:y should be list of argument AR's. If arguments are not passed, placeholder arguments x:: and y:: are used as left/right arg.
applyv =:((2+#@>@{:) $: ]) : {{
  'vb args' =. 2{.boxopen y NB. discard outer box.
  NB. TODO: extend later to allow passing verb as eclassid as well?
  yv=. (<vb) 5!:0          NB. rehydrate verb from AR.
  assert 3 4 e.~ yc=d nc yv NB. should be verb.
  assert x (3&=@] +. =) yc  NB. if yc dyad, x should be too
  assert (-.*#args)+.(#args)=x-2 NB. dyad should get 2 args, monad 1, if present.
  if. -. *#args do.
    NB. pre-create args for type& add already
    args=. (;:'x::y::'){.~2-x
    NB. store arg enodes
  else.
    NB. TODO: future: user gives arguments for analysis, rather than using placeholder arguments
    NB. could use type,shape to influence (conditional) rewrite rules.
    
  end.
  NB. add apply node with args, after adding y if needed.
  add 'a::';(add vb),([: adden '';~])&>args
}}

sym_z_ =: conew&'jsym'
