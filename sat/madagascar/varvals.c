/* 2012 (C) Jussi Rintanen, jrintanen.jr@gmail.com */

/* Functions to set literals and variables true and false, and to
   read their values.
   setlittrue
   setlitfalse
   unsetlit
   setvartrue
   setvarfalse
   unsetvar
   littruep
   litfalsep
   litunsetp
   vartruep
   varfalsep
   varunsetp
*/

/*************************************************************************/
/************************** one byte per variable ************************/
/*************************************************************************/

#ifdef REPRONE

#define VARVALUE(v) (sati->variableval[(v)])

inline int varunset(satinstance sati,int i) { return (VARVALUE(i) = UNASS); }
inline int varunsetp(satinstance sati,int i) { return (VARVALUE(i) == UNASS); }

inline void litsettrue(satinstance sati,int l) { VARVALUE(VAR(l)) = VALUE(l); }
inline void litunset(satinstance sati,int l) { VARVALUE(VAR(l)) = UNASS; }
inline int litunsetp(satinstance sati,int l) { return varunsetp(sati,VAR(l)); }

inline int littruep(satinstance sati,int l) { return (VARVALUE(VAR(l)) == VALUE(l)); }
inline int litfalsep(satinstance sati,int l) { return (VARVALUE(VAR(l)) == 1-VALUE(l)); }

/* Value of a state variable. */

inline int varvalue(satinstance sati,int v) { return VARVALUE(v); }
inline int vartruep(satinstance sati,int i) { return (VARVALUE(i) == 1); }
inline int varfalsep(satinstance sati,int i) { return (VARVALUE(i) == 0); }

#endif


/*************************************************************************/
/************************ 2+2 bits in a 32 bit word **********************/
/*************************************************************************/

#ifdef REPRTWO

/*
  Each literal has 2 bits. 1 = TRUE, 2 = FALSE, 0 = UNDEFINED
  This is quite a bit slower than representation 3. With DriverLog-16
  REPRTHREE total runtime is 80 per cent of REPRTWO.
 */

inline void setII(satinstance sati,int v,int val) {
  unsigned int index,slot,word,mask,b;
  index = v >> 3;
  slot = (v & 7) * 4;
  word = sati->variableval[index];
  mask = 15 << slot;
  b = val << slot;
  sati->variableval[index] = (word&(0xffffffff^mask))|b;
}

inline int getII(satinstance sati,int l) {
  unsigned int index,slot,word;
  index = l >> 4;
  slot = (l & 15) * 2;
  word = sati->variableval[index];
  return (word >> slot) & 3;
}

inline void litsettrue(satinstance sati,int l) {
  int val;
  val = 9-(l&1)*3;
  setII(sati,l >> 1,val);
}

inline void litsetfalse(satinstance sati,int l) {
  int val;
  val = 6+(l&1)*3;
  setII(sati,l >> 1,val);
}

inline void varsetfalse(satinstance sati,int v) {
  setII(sati,v,6); // 2 + (1 << 2)
}

inline void varsettrue(satinstance sati,int v) {
  setII(sati,v,9); // 1 + (2 << 2)
}

inline void litunset(satinstance sati,int l) {
  setII(sati,l >> 1,0);
}

inline void varunset(satinstance sati,int v) {
  setII(sati,v,0);
}

inline int littruep(satinstance sati,int l) {
  return (getII(sati,l) == 1);
}

inline int litfalsep(satinstance sati,int l) {
  return (getII(sati,l) == 2);
}

inline int litunsetp(satinstance sati,int l) {
  return (getII(sati,l) == 0);
}

inline int vartruep(satinstance sati,int v) {
  return (getII(sati,2*v) == 1);
}

inline int varfalsep(satinstance sati,int v) {
  return (getII(sati,2*v) == 2);
}

inline int varunsetp(satinstance sati,int v) {
  return (getII(sati,2*v) == 0);
}

inline int varvalue(satinstance sati,int v) {
  switch(getII(sati,2*v)) {
  case 1: return 1;
  case 2: return 0;
  default: return -1;
  };
  return -1;
}

#endif

/*************************************************************************/
/************** two bytes per variable, one for each literal *************/
/*************************************************************************/

#ifdef REPRTHREE

inline void litsettrue(satinstance sati,int l) {
  sati->variableval[l] = 1;
  sati->variableval[l^1] = 0;
}

inline void litsetfalse(satinstance sati,int l) {
  sati->variableval[l] = 0;
  sati->variableval[l^1] = 1;
}

inline void varsetfalse(satinstance sati,int v) {
  sati->variableval[v*2] = 0;
  sati->variableval[v*2+1] = 1;
}

inline void varsettrue(satinstance sati,int v) {
  sati->variableval[v*2] = 1;
  sati->variableval[v*2+1] = 0;
}

inline void litunset(satinstance sati,int l) {
  //  printf("UNSET: "); printTlit(sati,l); printf("\n");
  sati->variableval[l] = -1;
  sati->variableval[l^1] = -1;
}

inline void varunset(satinstance sati,int v) {
  //  printf("UNSET: "); printTlit(sati,PLIT(v)); printf("\n");
  sati->variableval[v*2] = -1;
  sati->variableval[v*2+1] = -1;
}

inline int littruep(satinstance sati,int l) {
  return (sati->variableval[l] == 1);
}

inline int litfalsep(satinstance sati,int l) {
  return (sati->variableval[l] == 0);
}

inline int litunsetp(satinstance sati,int l) {
  return (sati->variableval[l] == -1);
}

inline int vartruep(satinstance sati,int v) {
  return (sati->variableval[2*v] == 1);
}

inline int varfalsep(satinstance sati,int v) {
  return (sati->variableval[2*v] == 0);
}

inline int varunsetp(satinstance sati,int v) {
  return (sati->variableval[2*v] == -1);
}

inline int varvalue(satinstance sati,int v) {
  return (sati->variableval[2*v]);
}

#endif

#ifdef REPRFOUR

/*
  Each literal has 1 bit, indicating that it is true. If l and -l are both
  not true, then the literal is unassigned.
 */

/* Set bit true. */

inline void setI(satinstance sati,int l) {
  unsigned int index,slot,word;
  index = l >> 5;
  slot = l & 31;
  word = sati->variableval[index];
  sati->variableval[index] = word|(1 << slot);
}

/* Zero two bits. */

inline void unsetII(satinstance sati,int l) {
  unsigned int index,slot,word,mask,l0;
  l0 = l&0xfffffffe;
  index = l0 >> 5;
  slot = l0 & 31;
  word = sati->variableval[index];
  mask = 3 << slot;
  sati->variableval[index] = word&(0xffffffff^mask);
}

inline int getI(satinstance sati,int l) {
  unsigned int index,slot,word;
  index = l >> 5;
  slot = l & 31;
  word = sati->variableval[index];
  return word&(1 << slot);
}

inline int getII(satinstance sati,int l) {
  unsigned int index,slot,word;
  index = l >> 5;
  slot = l & 31;
  word = sati->variableval[index];
  return (word&(3 << slot)) >> slot;
}

/* If not set, set true and return 1. */

inline int litunset2true(satinstance sati,int l) {
  unsigned int index,slot,word,mask,l0,b;
  l0 = l&0xfffffffe;
  index = l0 >> 5;
  slot = l0 & 31;
  word = sati->variableval[index];
  mask = 3 << slot;
  if(word & mask) return 0;
  b = (l&1)+1;
  //  b = 1 << (l&1)+1;
  sati->variableval[index] = word|(b << slot);
  return 1;
}

inline void litsettrue(satinstance sati,int l) {
  setI(sati,l);
}

inline void litsetfalse(satinstance sati,int l) {
  setI(sati,l^1);
}

inline void varsetfalse(satinstance sati,int v) {
  setI(sati,2*v+1);
}

inline void varsettrue(satinstance sati,int v) {
  setI(sati,2*v);
}

inline void litunset(satinstance sati,int l) {
  unsetII(sati,l);
}

inline void varunset(satinstance sati,int v) {
  unsetII(sati,2*v);
}

inline int littruep(satinstance sati,int l) {
  return getI(sati,l);
}

inline int litfalsep(satinstance sati,int l) {
  return getI(sati,l^1);
}

inline int litunsetp(satinstance sati,int l) {
  return (getII(sati,l&0xfffffffe) == 0);
}

inline int vartruep(satinstance sati,int v) {
  return getI(sati,2*v);
}

inline int varfalsep(satinstance sati,int v) {
  return getI(sati,2*v+1);
}

inline int varunsetp(satinstance sati,int v) {
  return (getII(sati,2*v) == 0);
}

inline int varvalue(satinstance sati,int v) {
  switch(getII(sati,2*v)) {
  case 0: return -1;
  case 1: return 1;
  default: return 0;
  };
  return -1;
}

#endif

inline int tvarvalue(satinstance sati,int v,int t) { return varvalue(sati,TVAR(v,t)); }
inline int tvartime(satinstance sati,int vt) { return vt/sati->nOfVarsPerTime; }
inline int tvarvar(satinstance sati,int vt) { return vt%sati->nOfVarsPerTime; }

inline int untimevar(satinstance sati,int v) { return (v%(sati->nOfVarsPerTime)); }
inline int litwithtime(satinstance sati,int l,int t) {
  //  return (((l >> 1) + sati->nOfVarsPerTime * t) << 1) | (l&1);
  return l + 2 * sati->nOfVarsPerTime * t;
}
inline int varwithtime(satinstance sati,int v,int t) {
  return v + sati->nOfVarsPerTime * t;
}


inline int tvartruep(satinstance sati,int v,int t) {
  return vartruep(sati,varwithtime(sati,v,t));
}

inline int tvarfalsep(satinstance sati,int v,int t) {
  return varfalsep(sati,varwithtime(sati,v,t));
}

inline int tvarunsetp(satinstance sati,int v,int t) {
  return varunsetp(sati,varwithtime(sati,v,t));
}


inline int tlittruep(satinstance sati,int l,int t) {
  return littruep(sati,litwithtime(sati,l,t));
}

inline int tlitfalsep(satinstance sati,int l,int t) {
  return litfalsep(sati,litwithtime(sati,l,t));
}

inline int tlitunsetp(satinstance sati,int l,int t) {
  return litunsetp(sati,litwithtime(sati,l,t));
}
