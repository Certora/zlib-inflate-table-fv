import InflateTableBody
open CC Inftrees InflateTable.Body

-- loop1
example : loop1 =
(Stmt.Sloop
            (Stmt.Ssequence
              (Stmt.Sifthenelse (Expr.Ebinop Binop.Ole
                                  (Expr.Etempvar _len tuint)
                                  (Expr.Econst_int (Integers.Int.repr 15) tint)
                                  tint)
                Stmt.Sskip
                Stmt.Sbreak)
              (Stmt.Sassign
                (Expr.Ederef
                  (Expr.Ebinop Binop.Oadd
                    (Expr.Evar _count (tarray tushort 16))
                    (Expr.Etempvar _len tuint) (tptr tushort)) tushort)
                (Expr.Econst_int (Integers.Int.repr 0) tint)))
            (Stmt.Sset _len
              (Expr.Ebinop Binop.Oadd (Expr.Etempvar _len tuint)
                (Expr.Econst_int (Integers.Int.repr 1) tint) tuint)))
  := rfl

-- loop2
example : loop2 =
(Stmt.Sloop
              (Stmt.Ssequence
                (Stmt.Sifthenelse (Expr.Ebinop Binop.Olt
                                    (Expr.Etempvar _sym tuint)
                                    (Expr.Etempvar _codes tuint) tint)
                  Stmt.Sskip
                  Stmt.Sbreak)
                (Stmt.Ssequence
                  (Stmt.Sset _t'34
                    (Expr.Ederef
                      (Expr.Ebinop Binop.Oadd
                        (Expr.Etempvar _lens (tptr tushort))
                        (Expr.Etempvar _sym tuint) (tptr tushort)) tushort))
                  (Stmt.Ssequence
                    (Stmt.Sset _t'35
                      (Expr.Ederef
                        (Expr.Ebinop Binop.Oadd
                          (Expr.Etempvar _lens (tptr tushort))
                          (Expr.Etempvar _sym tuint) (tptr tushort)) tushort))
                    (Stmt.Ssequence
                      (Stmt.Sset _t'36
                        (Expr.Ederef
                          (Expr.Ebinop Binop.Oadd
                            (Expr.Evar _count (tarray tushort 16))
                            (Expr.Etempvar _t'35 tushort) (tptr tushort))
                          tushort))
                      (Stmt.Sassign
                        (Expr.Ederef
                          (Expr.Ebinop Binop.Oadd
                            (Expr.Evar _count (tarray tushort 16))
                            (Expr.Etempvar _t'34 tushort) (tptr tushort))
                          tushort)
                        (Expr.Ebinop Binop.Oadd (Expr.Etempvar _t'36 tushort)
                          (Expr.Econst_int (Integers.Int.repr 1) tint) tint))))))
              (Stmt.Sset _sym
                (Expr.Ebinop Binop.Oadd (Expr.Etempvar _sym tuint)
                  (Expr.Econst_int (Integers.Int.repr 1) tint) tuint)))
  := rfl

-- loop3
example : loop3 =
(Stmt.Sloop
                  (Stmt.Ssequence
                    (Stmt.Sifthenelse (Expr.Ebinop Binop.Oge
                                        (Expr.Etempvar _max tuint)
                                        (Expr.Econst_int (Integers.Int.repr 1) tint)
                                        tint)
                      Stmt.Sskip
                      Stmt.Sbreak)
                    (Stmt.Ssequence
                      (Stmt.Sset _t'33
                        (Expr.Ederef
                          (Expr.Ebinop Binop.Oadd
                            (Expr.Evar _count (tarray tushort 16))
                            (Expr.Etempvar _max tuint) (tptr tushort))
                          tushort))
                      (Stmt.Sifthenelse (Expr.Ebinop Binop.One
                                          (Expr.Etempvar _t'33 tushort)
                                          (Expr.Econst_int (Integers.Int.repr 0) tint)
                                          tint)
                        Stmt.Sbreak
                        Stmt.Sskip)))
                  (Stmt.Sset _max
                    (Expr.Ebinop Binop.Osub (Expr.Etempvar _max tuint)
                      (Expr.Econst_int (Integers.Int.repr 1) tint) tuint)))
  := rfl

-- maxZeroBlock
example : maxZeroBlock =
(Stmt.Sifthenelse (Expr.Ebinop Binop.Oeq
                                      (Expr.Etempvar _max tuint)
                                      (Expr.Econst_int (Integers.Int.repr 0) tint)
                                      tint)
                    (Stmt.Ssequence
                      (Stmt.Sassign
                        (Expr.Efield
                          (Expr.Evar _here (Ty.Tstruct __1353 noattr)) _op
                          tuchar)
                        (Expr.Ecast
                          (Expr.Econst_int (Integers.Int.repr 64) tint)
                          tuchar))
                      (Stmt.Ssequence
                        (Stmt.Sassign
                          (Expr.Efield
                            (Expr.Evar _here (Ty.Tstruct __1353 noattr))
                            _bits tuchar)
                          (Expr.Ecast
                            (Expr.Econst_int (Integers.Int.repr 1) tint)
                            tuchar))
                        (Stmt.Ssequence
                          (Stmt.Sassign
                            (Expr.Efield
                              (Expr.Evar _here (Ty.Tstruct __1353 noattr))
                              _val tushort)
                            (Expr.Ecast
                              (Expr.Econst_int (Integers.Int.repr 0) tint)
                              tushort))
                          (Stmt.Ssequence
                            (Stmt.Ssequence
                              (Stmt.Ssequence
                                (Stmt.Sset _t'1
                                  (Expr.Ederef
                                    (Expr.Etempvar _table (tptr (tptr (Ty.Tstruct __1353 noattr))))
                                    (tptr (Ty.Tstruct __1353 noattr))))
                                (Stmt.Sassign
                                  (Expr.Ederef
                                    (Expr.Etempvar _table (tptr (tptr (Ty.Tstruct __1353 noattr))))
                                    (tptr (Ty.Tstruct __1353 noattr)))
                                  (Expr.Ebinop Binop.Oadd
                                    (Expr.Etempvar _t'1 (tptr (Ty.Tstruct __1353 noattr)))
                                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                                    (tptr (Ty.Tstruct __1353 noattr)))))
                              (Stmt.Sassign
                                (Expr.Ederef
                                  (Expr.Etempvar _t'1 (tptr (Ty.Tstruct __1353 noattr)))
                                  (Ty.Tstruct __1353 noattr))
                                (Expr.Evar _here (Ty.Tstruct __1353 noattr))))
                            (Stmt.Ssequence
                              (Stmt.Ssequence
                                (Stmt.Ssequence
                                  (Stmt.Sset _t'2
                                    (Expr.Ederef
                                      (Expr.Etempvar _table (tptr (tptr (Ty.Tstruct __1353 noattr))))
                                      (tptr (Ty.Tstruct __1353 noattr))))
                                  (Stmt.Sassign
                                    (Expr.Ederef
                                      (Expr.Etempvar _table (tptr (tptr (Ty.Tstruct __1353 noattr))))
                                      (tptr (Ty.Tstruct __1353 noattr)))
                                    (Expr.Ebinop Binop.Oadd
                                      (Expr.Etempvar _t'2 (tptr (Ty.Tstruct __1353 noattr)))
                                      (Expr.Econst_int (Integers.Int.repr 1) tint)
                                      (tptr (Ty.Tstruct __1353 noattr)))))
                                (Stmt.Sassign
                                  (Expr.Ederef
                                    (Expr.Etempvar _t'2 (tptr (Ty.Tstruct __1353 noattr)))
                                    (Ty.Tstruct __1353 noattr))
                                  (Expr.Evar _here (Ty.Tstruct __1353 noattr))))
                              (Stmt.Ssequence
                                (Stmt.Sassign
                                  (Expr.Ederef
                                    (Expr.Etempvar _bits (tptr tuint)) tuint)
                                  (Expr.Econst_int (Integers.Int.repr 1) tint))
                                (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 0) tint)))))))))
                    Stmt.Sskip)
  := rfl

-- loop4
example : loop4 =
(Stmt.Sloop
                        (Stmt.Ssequence
                          (Stmt.Sifthenelse (Expr.Ebinop Binop.Olt
                                              (Expr.Etempvar _min tuint)
                                              (Expr.Etempvar _max tuint)
                                              tint)
                            Stmt.Sskip
                            Stmt.Sbreak)
                          (Stmt.Ssequence
                            (Stmt.Sset _t'32
                              (Expr.Ederef
                                (Expr.Ebinop Binop.Oadd
                                  (Expr.Evar _count (tarray tushort 16))
                                  (Expr.Etempvar _min tuint) (tptr tushort))
                                tushort))
                            (Stmt.Sifthenelse (Expr.Ebinop Binop.One
                                                (Expr.Etempvar _t'32 tushort)
                                                (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                tint)
                              Stmt.Sbreak
                              Stmt.Sskip)))
                        (Stmt.Sset _min
                          (Expr.Ebinop Binop.Oadd (Expr.Etempvar _min tuint)
                            (Expr.Econst_int (Integers.Int.repr 1) tint)
                            tuint)))
  := rfl

-- loop5
example : loop5 =
(Stmt.Sloop
                              (Stmt.Ssequence
                                (Stmt.Sifthenelse (Expr.Ebinop Binop.Ole
                                                    (Expr.Etempvar _len tuint)
                                                    (Expr.Econst_int (Integers.Int.repr 15) tint)
                                                    tint)
                                  Stmt.Sskip
                                  Stmt.Sbreak)
                                (Stmt.Ssequence
                                  (Stmt.Sset _left
                                    (Expr.Ebinop Binop.Oshl
                                      (Expr.Etempvar _left tint)
                                      (Expr.Econst_int (Integers.Int.repr 1) tint)
                                      tint))
                                  (Stmt.Ssequence
                                    (Stmt.Ssequence
                                      (Stmt.Sset _t'31
                                        (Expr.Ederef
                                          (Expr.Ebinop Binop.Oadd
                                            (Expr.Evar _count (tarray tushort 16))
                                            (Expr.Etempvar _len tuint)
                                            (tptr tushort)) tushort))
                                      (Stmt.Sset _left
                                        (Expr.Ebinop Binop.Osub
                                          (Expr.Etempvar _left tint)
                                          (Expr.Etempvar _t'31 tushort) tint)))
                                    (Stmt.Sifthenelse (Expr.Ebinop Binop.Olt
                                                        (Expr.Etempvar _left tint)
                                                        (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                        tint)
                                      (Stmt.Sreturn (some (Expr.Eunop Unop.Oneg
                                                            (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                            tint)))
                                      Stmt.Sskip))))
                              (Stmt.Sset _len
                                (Expr.Ebinop Binop.Oadd
                                  (Expr.Etempvar _len tuint)
                                  (Expr.Econst_int (Integers.Int.repr 1) tint)
                                  tuint)))
  := rfl

-- chk6
example : chk6 =
(Stmt.Ssequence
                              (Stmt.Sifthenelse (Expr.Ebinop Binop.Ogt
                                                  (Expr.Etempvar _left tint)
                                                  (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                  tint)
                                (Stmt.Sifthenelse (Expr.Ebinop Binop.Oeq
                                                    (Expr.Etempvar _type tint)
                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                    tint)
                                  (Stmt.Sset _t'3
                                    (Expr.Ecast
                                      (Expr.Econst_int (Integers.Int.repr 1) tint)
                                      tbool))
                                  (Stmt.Ssequence
                                    (Stmt.Sset _t'3
                                      (Expr.Ecast
                                        (Expr.Ebinop Binop.One
                                          (Expr.Etempvar _max tuint)
                                          (Expr.Econst_int (Integers.Int.repr 1) tint)
                                          tint) tbool))
                                    (Stmt.Sset _t'3
                                      (Expr.Ecast (Expr.Etempvar _t'3 tint)
                                        tbool))))
                                (Stmt.Sset _t'3
                                  (Expr.Econst_int (Integers.Int.repr 0) tint)))
                              (Stmt.Sifthenelse (Expr.Etempvar _t'3 tint)
                                (Stmt.Sreturn (some (Expr.Eunop Unop.Oneg
                                                      (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                      tint)))
                                Stmt.Sskip))
  := rfl

-- offs1Init
example : offs1Init =
(Stmt.Sassign
                                (Expr.Ederef
                                  (Expr.Ebinop Binop.Oadd
                                    (Expr.Evar _offs (tarray tushort 16))
                                    (Expr.Econst_int (Integers.Int.repr 1) tint)
                                    (tptr tushort)) tushort)
                                (Expr.Econst_int (Integers.Int.repr 0) tint))
  := rfl

-- loop6
example : loop6 =
(Stmt.Sloop
                                    (Stmt.Ssequence
                                      (Stmt.Sifthenelse (Expr.Ebinop Binop.Olt
                                                          (Expr.Etempvar _len tuint)
                                                          (Expr.Econst_int (Integers.Int.repr 15) tint)
                                                          tint)
                                        Stmt.Sskip
                                        Stmt.Sbreak)
                                      (Stmt.Ssequence
                                        (Stmt.Sset _t'29
                                          (Expr.Ederef
                                            (Expr.Ebinop Binop.Oadd
                                              (Expr.Evar _offs (tarray tushort 16))
                                              (Expr.Etempvar _len tuint)
                                              (tptr tushort)) tushort))
                                        (Stmt.Ssequence
                                          (Stmt.Sset _t'30
                                            (Expr.Ederef
                                              (Expr.Ebinop Binop.Oadd
                                                (Expr.Evar _count (tarray tushort 16))
                                                (Expr.Etempvar _len tuint)
                                                (tptr tushort)) tushort))
                                          (Stmt.Sassign
                                            (Expr.Ederef
                                              (Expr.Ebinop Binop.Oadd
                                                (Expr.Evar _offs (tarray tushort 16))
                                                (Expr.Ebinop Binop.Oadd
                                                  (Expr.Etempvar _len tuint)
                                                  (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                  tuint) (tptr tushort))
                                              tushort)
                                            (Expr.Ebinop Binop.Oadd
                                              (Expr.Etempvar _t'29 tushort)
                                              (Expr.Etempvar _t'30 tushort)
                                              tint)))))
                                    (Stmt.Sset _len
                                      (Expr.Ebinop Binop.Oadd
                                        (Expr.Etempvar _len tuint)
                                        (Expr.Econst_int (Integers.Int.repr 1) tint)
                                        tuint)))
  := rfl

-- loop7
example : loop7 =
(Stmt.Sloop
                                      (Stmt.Ssequence
                                        (Stmt.Sifthenelse (Expr.Ebinop Binop.Olt
                                                            (Expr.Etempvar _sym tuint)
                                                            (Expr.Etempvar _codes tuint)
                                                            tint)
                                          Stmt.Sskip
                                          Stmt.Sbreak)
                                        (Stmt.Ssequence
                                          (Stmt.Sset _t'26
                                            (Expr.Ederef
                                              (Expr.Ebinop Binop.Oadd
                                                (Expr.Etempvar _lens (tptr tushort))
                                                (Expr.Etempvar _sym tuint)
                                                (tptr tushort)) tushort))
                                          (Stmt.Sifthenelse (Expr.Ebinop Binop.One
                                                              (Expr.Etempvar _t'26 tushort)
                                                              (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                              tint)
                                            (Stmt.Ssequence
                                              (Stmt.Ssequence
                                                (Stmt.Ssequence
                                                  (Stmt.Sset _t'28
                                                    (Expr.Ederef
                                                      (Expr.Ebinop Binop.Oadd
                                                        (Expr.Etempvar _lens (tptr tushort))
                                                        (Expr.Etempvar _sym tuint)
                                                        (tptr tushort))
                                                      tushort))
                                                  (Stmt.Sset _t'4
                                                    (Expr.Ederef
                                                      (Expr.Ebinop Binop.Oadd
                                                        (Expr.Evar _offs (tarray tushort 16))
                                                        (Expr.Etempvar _t'28 tushort)
                                                        (tptr tushort))
                                                      tushort)))
                                                (Stmt.Ssequence
                                                  (Stmt.Sset _t'27
                                                    (Expr.Ederef
                                                      (Expr.Ebinop Binop.Oadd
                                                        (Expr.Etempvar _lens (tptr tushort))
                                                        (Expr.Etempvar _sym tuint)
                                                        (tptr tushort))
                                                      tushort))
                                                  (Stmt.Sassign
                                                    (Expr.Ederef
                                                      (Expr.Ebinop Binop.Oadd
                                                        (Expr.Evar _offs (tarray tushort 16))
                                                        (Expr.Etempvar _t'27 tushort)
                                                        (tptr tushort))
                                                      tushort)
                                                    (Expr.Ebinop Binop.Oadd
                                                      (Expr.Etempvar _t'4 tushort)
                                                      (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                      tint))))
                                              (Stmt.Sassign
                                                (Expr.Ederef
                                                  (Expr.Ebinop Binop.Oadd
                                                    (Expr.Etempvar _work (tptr tushort))
                                                    (Expr.Etempvar _t'4 tushort)
                                                    (tptr tushort)) tushort)
                                                (Expr.Ecast
                                                  (Expr.Etempvar _sym tuint)
                                                  tushort)))
                                            Stmt.Sskip)))
                                      (Stmt.Sset _sym
                                        (Expr.Ebinop Binop.Oadd
                                          (Expr.Etempvar _sym tuint)
                                          (Expr.Econst_int (Integers.Int.repr 1) tint)
                                          tuint)))
  := rfl

-- switchStmt
example : switchStmt =
(Stmt.Sswitch (Expr.Etempvar _type tint)
                                      (LStmts.LScons (some 0)
                                        (Stmt.Ssequence
                                          (Stmt.Sset _match
                                            (Expr.Econst_int (Integers.Int.repr 20) tint))
                                          Stmt.Sbreak)
                                        (LStmts.LScons (some 1)
                                          (Stmt.Ssequence
                                            (Stmt.Sset _base
                                              (Expr.Evar _lbase (tarray tushort 31)))
                                            (Stmt.Ssequence
                                              (Stmt.Sset _extra
                                                (Expr.Evar _lext (tarray tushort 31)))
                                              (Stmt.Ssequence
                                                (Stmt.Sset _match
                                                  (Expr.Econst_int (Integers.Int.repr 257) tint))
                                                Stmt.Sbreak)))
                                          (LStmts.LScons (some 2)
                                            (Stmt.Ssequence
                                              (Stmt.Sset _base
                                                (Expr.Evar _dbase (tarray tushort 32)))
                                              (Stmt.Sset _extra
                                                (Expr.Evar _dext (tarray tushort 32))))
                                            LStmts.LSnil))))
  := rfl

-- enoughChk
example : enoughChk =
(Stmt.Ssequence
                                                          (Stmt.Ssequence
                                                            (Stmt.Sifthenelse 
                                                              (Expr.Ebinop Binop.Oeq
                                                                (Expr.Etempvar _type tint)
                                                                (Expr.Econst_int (Integers.Int.repr 1) tint)
                                                                tint)
                                                              (Stmt.Sset _t'5
                                                                (Expr.Ecast
                                                                  (Expr.Ebinop Binop.Ogt
                                                                    (Expr.Etempvar _used tuint)
                                                                    (Expr.Econst_int (Integers.Int.repr 852) tint)
                                                                    tint)
                                                                  tbool))
                                                              (Stmt.Sset _t'5
                                                                (Expr.Econst_int (Integers.Int.repr 0) tint)))
                                                            (Stmt.Sifthenelse (Expr.Etempvar _t'5 tint)
                                                              (Stmt.Sset _t'6
                                                                (Expr.Econst_int (Integers.Int.repr 1) tint))
                                                              (Stmt.Sifthenelse 
                                                                (Expr.Ebinop Binop.Oeq
                                                                  (Expr.Etempvar _type tint)
                                                                  (Expr.Econst_int (Integers.Int.repr 2) tint)
                                                                  tint)
                                                                (Stmt.Ssequence
                                                                  (Stmt.Sset _t'6
                                                                    (Expr.Ecast
                                                                    (Expr.Ebinop Binop.Ogt
                                                                    (Expr.Etempvar _used tuint)
                                                                    (Expr.Econst_int (Integers.Int.repr 592) tint)
                                                                    tint)
                                                                    tbool))
                                                                  (Stmt.Sset _t'6
                                                                    (Expr.Ecast
                                                                    (Expr.Etempvar _t'6 tint)
                                                                    tbool)))
                                                                (Stmt.Sset _t'6
                                                                  (Expr.Ecast
                                                                    (Expr.Econst_int (Integers.Int.repr 0) tint)
                                                                    tbool)))))
                                                          (Stmt.Sifthenelse (Expr.Etempvar _t'6 tint)
                                                            (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 1) tint)))
                                                            Stmt.Sskip))
  := rfl
