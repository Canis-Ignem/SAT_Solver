-- Decidir si una proposici�n es satisfactible.
-- Esto es lo que hacen los famosos SAT-solvers 
-- (de un modo m�s eficiente)

-- El tipo Prop

infixr 3 :& 
infixr 2 :| 
infixr 1 :->, :<->
-- C, X, Not tiene m�xima prioridad por que las 
-- funciones (constructores) en Haskell la tienen
data Prop =   C Bool    -- constante booleana
            | X String  -- variable proposicional
            | Not Prop         -- negaci�n
            | Prop :& Prop     -- conjunci�n
            | Prop :| Prop     -- disyunci�n
            | Prop :-> Prop    -- implicaci�n
            | Prop :<-> Prop   -- doble implicaci�n
            -- deriving Show

-- Ejemplos
prop1 = X "p" :| Not (X "p")
prop2 = X "p" :& Not (X "p")
prop3 = X "p" :| C False :-> C False   
        -- (p | False) -> False
        -- es satisfactible, pero no tautolog�a
prop4 = X "p" :-> C False :| X "q"
        -- p -> ( False | q)
        -- es satisfactible, pero no tautolog�a     
prop5 = (X "p" :-> X "q") :& X "p" :->  X "q"
prop6 = prop4 :& X "r" :-> X "a" :| prop5 

-- Formalizaci�n de un argumento
{- A, B y C son sospechosos de haber robado.
Las investigaciones concluyen que 
1) Alguno de los tres es culpable
2) Si A es culpable entonces B es inocente
3) B es inocente si y solo si A y C no son los dos culpables
Entonces es imposible que B sea culpable.
Es decir, 1) :& 2) :& 3) : "B es culpable" 
forman un conjunto insatisfactible
-}

p1 = X "culpA" :| X "culpB" :| X "culpC"
p2 = X "culpA" :-> Not(X "culpB")
p3 = Not (X "culpB") :<-> Not(X "culpA" :& X "culpC")
conjetura = Not (X "culpB")                                  
argumento = p1 :& p2 :& p3 :& Not conjetura 
  -- si argumento no tiene modelo, entonces {p1,p2,p3} ==> conjetura
modelo = p1 :& p2 :& p3 :& conjetura       
  -- si es sat, hay un modelo de {p1,p2,p3,conjetura}

instance Show Prop where
      show p 
       = case p of
           (C b)        -> show b
           (X s)        -> s
           (Not p)      -> showP "~" [p]
           (p1 :& p2)   -> showP " & "  [p1,p2] 
           (p1 :| p2)   -> showP " | "  [p1,p2]     
           (p1 :-> p2)  -> showP " -> " [p1,p2]  
           (p1 :<-> p2) -> showP " <-> " [p1,p2]   
           where showP s [p] = if esSimple p then s ++ show p 
                               else s ++ "(" ++ show p ++ ")"
                 showP s [p1,p2] 
                    | esSimple p1 && esSimple p2 = show p1++s++show p2
                    | esSimple p1 = show p1++" "++ s++"("++show p2++")"
                    | esSimple p2 = "("++show p1++")"++s++ " "++ show p2  
                    | otherwise   = "("++show p1++")"
                                     ++s 
                                     ++"("++show p2++")"
                 esSimple (C b) = True
                 esSimple (X s) = True
                 esSimple (Not p) = True 
                 esSimple _ = False
 
-- El tipo Subs
type Subs = [(String,Bool)]
-- Una substituci�n asocia a cada variable (String) 
-- un valor de verdad (Bool)
-- type Subs = String -> Bool
-- Ejemplos:
sb1 = [("p",True),("q",False),("r",True),("a",False)]
      -- sb1 "p" = True
      -- sb1 "q" = False
      -- sb1 "r" = True
      -- sb1 "a" = False
sb2 = [("culpA",True),("culpB",False),("culpC",True)]

-- 1.- La funci�n evaluar
evaluar :: Subs -> Prop -> Bool
evaluar _ (C b) = b
evaluar sb (X s) = apply sb s
                   where 
                   apply sbs s 
                      = (snd. head) (dropWhile ((/=s).fst) sb)
evaluar sb (Not p) = not (evaluar sb p)
evaluar sb (p1 :& p2) = evaluar sb p1 && evaluar sb p2
evaluar sb (p1 :| p2) = evaluar sb p1 || evaluar sb p2
evaluar sb (p1 :-> p2) = not (evaluar sb p1) || evaluar sb p2
evaluar sb (p1 :<-> p2) = let evp1 = evaluar sb p1
                              evp2 = evaluar sb p2
                          in (evp1 && evp2)||(not(evp1) && not(evp2))
                                 
-- 2.- La lista de todas las substituciones 
--     que son posibles modelos de una proposici�n

vars:: Prop -> [String]
-- (vars p) sea la lista de todas las variable (con repeticiones)
-- de la proposicion p
vars (C _) = []
vars (X x) = [x]
vars (Not p) = vars p
vars (p1 :& p2) = (vars p1) ++ (vars p2)
vars (p1 :| p2) = (vars p1) ++ (vars p2)
vars (p1 :-> p2) = (vars p1) ++ (vars p2)
vars (p1 :<-> p2) = (vars p1) ++ (vars p2)

-- para quitar las repetidas de (vars p)
quitarRep :: (Eq a) => [a] -> [a]
quitarRep [] = []
quitarRep (c:cs) = c : (filter (/=c) (quitarRep cs))
                 -- = c : quitarRep (filter (/=c) cs)

-- lisbool 1 = [[True], [False]]
-- lisbool 2 = [[True,True], [True,False],[False,True], [False,False]]
lisBool :: Int -> [[Bool]]
lisBool 1 = [[True], [False]]
lisBool n = (map (True:) list) ++ (map (False:) list)
            where list = lisBool (n-1)

listSubs :: Prop -> [Subs]
-- (listSubs p) es lista de todas las posibles substituciones 
-- de las variables de p
listSubs p = [zip listvar listbool | listbool <- (lisBool n) ]
              where listvar = (quitarRep . vars) p 
                    n = length listvar              
            
-- 3.- Las funciones principales: sat, modelos, taut

sat:: Prop -> Bool
-- (sat p) es True si y solo si p es satisfactible 
-- i.e. es cierta para al menos una substituci�n
sat p -- = or [evaluar s p | s <- listSubs p]
      -- = foldr (||) False [evaluar s p | s <- listSubs p]
      = or (map ((flip evaluar) p) (listSubs p))
-- evaluar :: Subs -> Prop -> Bool
-- (flip evaluar) :: Prop -> Subs -> Bool
                                  
modelos :: Prop -> [Subs]
-- (modelos p) es la lista de todas las substituciones 
-- que hacen a p cierta
modelos p = [s | s <- listSubs p, evaluar s p]

-- EJERCICIO: definir modelos usando el flip de evaluar

taut:: Prop -> Bool
-- (taut p) es True si y solo si p es una tautolog�a 
-- i.e. es cierta para cualquier substituci�n.
      -- = and [evaluar s p | s <- listSubs p]
      -- = foldr (&&) True [evaluar s p | s <- listSubs p]
taut p = and (map ((flip evaluar) p) (listSubs p))

-- EJERCICIO: HACER TODOS LOS AJUSTES NECESARIOS EN EL PROGRAMA DE ARRIBA
-- PARA QUE EL TIPO Subs SEA String -> Bool

graphOf :: (Num a, Enum a) => (a -> b) -> [(a, b)]
graphOf f = [(e,f e) | e <-[0..]]
          -- = [(e,v) | e <- [0..], v <- [f e]]
          
fromGraph:: Eq a => [(a,b)] -> a -> b
fromGraph m i = (snd . head) (filter ((==i).fst) m)
-- m :: [(a,b)]
-- i :: a
-- (filter ((==i).fst) m):: [(a,b)] 
-- (filter ((==i).fst) m) => [(i,v), ...]
-- (snd . head) [(i,v), ...] => v
