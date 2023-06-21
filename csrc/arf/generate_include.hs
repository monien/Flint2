import Control.Monad

import Text.ParserCombinators.Parsec

main = do
  contents <- readFile "arf.h"
  forM_ (lines contents) $ \line -> do
    putStrLn line
  case parse arf_inline "" contents of
    Right s -> print s
    _ -> error $ "no parse."
    
arf_inline = do
  try (string "ARF_INLINE")
  spaces
  (f, args, r) <- c_function 
  spaces
  return (f, args, r)

c_function = do
  r <- c_type
  spaces
  f <- c_identifier
  spaces
  args <- c_arguments
  spaces
  return (f, args, r)

c_function_body = do
  string "{"
  string "}"

c_arguments = c_arg_void <|> c_args

c_args = do
  string "("
  spaces 
  args <- sepBy c_arg (char ',')
  spaces
  string ")"
  return args
  
c_arg_void = do
  try ( do
          string "("
          spaces
          string "void"
          spaces
          string ")")
  return []

c_arg = do
  spaces
  t <- c_type
  spaces
  n <- c_identifier
  spaces
  return (t, n)

c_type = do
  q <- optionMaybe c_type_qualifier
  spaces
  m <- optionMaybe c_type_modifier
  spaces
  t <- c_identifier
  spaces
  p <- many c_pointer
  spaces
  optional c_type_qualifier
  spaces
  return (q, m, t, p)
  
c_identifier = do
   first <- letter <|> (char '_')
   rest <- many (alphaNum <|> (char '_'))
   return $ first : rest

c_type_qualifier = c_const <|> c_volatile <|> c_enum

c_const = do
  q <- try (string "const")
  spaces
  return q

c_volatile = do
  q <- try (string "volatile")
  spaces
  return q

c_enum = do
  q <- try (string "enum")
  spaces
  return q

c_pointer = do
  try $ do
    optionMaybe c_const
    spaces
    p <- try (char '*')
    spaces
    return p

c_type_modifier = c_signed <|> c_unsigned

c_signed = do
  m <- try (string "signed")
  spaces
  return m

c_unsigned = do
  m <- try (string "unsigned")
  spaces
  return m

--------------------------------------------------------------------------------

main' = do
  contents <- readFile "inlines.c"
  let l = lines contents
  writeFile "tmp.c" $ unlines $ f $ lines contents
  contents <- readFile "fun"
  writeFile "s"
    $ unlines
    $ map (\x -> "s/" ++ init x ++ "/" ++ x ++ "/g")
    $ lines contents 

f [] = []
f [_] = []
f (x:y:xs) =
  if not (null y) && head y == 'a' then
    [x ++ " " ++ y ++ ";"] ++ f xs
  else
    f (y:xs)

