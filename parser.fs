//
// Parser for SimpleC programs.  This component checks 
// the input program to see if it meets the syntax rules
// of SimpleC.  The parser returns a string denoting
// success or failure. 
//
// Returns: the string "success" if the input program is
// legal, otherwise the string "syntax_error: ..." is
// returned denoting an invalid SimpleC program.
//
// Viraj Saudagar 


namespace compiler

module parser =

  //
  // matchToken
  //

  // Returns true if the string beings with the pattern provided and false if not
  let beginswith (pattern: string) (literal: string) = 
    literal.StartsWith (pattern)
  
  let private matchToken expected_token tokens =
    //
    // if the next token matches the expected token,  
    // keep parsing by returning the rest of the tokens.
    // Otherwise throw an exception because there's a 
    // syntax error, effectively stopping compilation
    // at the first error.
    //
    let next_token = List.head tokens

    if expected_token = "identifier" then
      // we are expecting identifier:_
      if beginswith "identifier" next_token then
        List.tail tokens
      else
        failwith ("expecting identifier, but found " + next_token)
    elif expected_token = "int_literal" then
      // expecting int_literal:_ 
      if beginswith "int_literal" next_token then
        List.tail tokens
      else
        failwith ("expecting identifier or literal, but found " + next_token)
    elif expected_token = "str_literal" then
      // expecting str_literal:_
      if beginswith "str_literal" next_token then
        List.tail tokens
      else
        failwith ("expecting identifier or literal, but found " + next_token)
    elif expected_token = "real_literal" then
      // expecting real_literal:_ 
      if beginswith "real_literal" next_token then
        List.tail tokens
      else
        failwith ("expecting identifier or literal, but found " + next_token)
    else
      if expected_token = next_token then  
        List.tail tokens
      else
        failwith ("expecting " + expected_token + ", but found " + next_token)


  // First calls stmt to handle initial stmt then calls morestmts from result of last call
  let rec private stmts tokens =     
    let T2 = stmt tokens
    morestmts T2

  // all possible stmt options and their recursive descent functions are called depending on which one is matched with
  and private stmt tokens = 
    let nextToken = List.head tokens

    if nextToken = ";" then
      let T2 = empty tokens
      T2
    elif nextToken = "int" then
      let T3 = vardeclInt tokens
      T3
    elif nextToken = "cin" then
      let T4 = input tokens
      T4
    elif nextToken = "cout" then
      let T5 = output tokens
      T5
    elif beginswith "identifier" nextToken then
      let T6 = assignment tokens
      T6
    elif nextToken = "if" then
      let T7 = ifstmt tokens
      T7
    elif nextToken = "real" then
      let T8 = vardeclReal tokens
      T8
    else
      failwith ("expecting statement, but found " + nextToken)

  and private vardeclReal tokens = 
    let T2 = matchToken "real" tokens
    let T3 = matchToken "identifier" T2
    let T4 = matchToken ";" T3
    T4
    

  and private vardeclInt tokens = 
    let T2 = matchToken "int" tokens
    let T3 = matchToken "identifier" T2
    let T4 = matchToken ";" T3
    T4
  
  and private ifstmt tokens = 
    let T2 = matchToken "if" tokens
    let T3 = matchToken "(" T2
    let T4 = condition T3
    let T5 = matchToken ")" T4
    let T6 = thenpart T5
    let T7 = elsepart T6
    T7
  
  and private condition tokens = 
    expr tokens
  
  and private thenpart tokens = 
    stmt tokens
  
  and private elsepart tokens = 
    let nextToken = List.head tokens

    if nextToken = "else" then
      let T2 = matchToken "else" tokens
      let T3 = stmt T2
      T3
    else
      tokens

  and private assignment tokens = 
    let nextToken = List.head tokens

    let T2 = matchToken "identifier" tokens
    let T3 = matchToken "=" T2
    let T4 = expr T3
    let T5 = matchToken ";" T4
    T5
  
  and private expr tokens = 
    // match first required exprvalue
    let T2 = exprvalue tokens
    let nextToken = List.head T2

    if nextToken = "+" || nextToken = "-" || nextToken = "*" || nextToken = "/" || nextToken = "^" || nextToken = "<" || nextToken = "<=" || nextToken = ">" || nextToken = ">=" || nextToken = "==" || nextToken = "!=" then
      let T3 = exprop T2
      let T4 = exprvalue T3
      T4
    else
      T2
      

  and private exprop tokens = 
    let nextToken = List.head tokens

    match nextToken with
    | "+" -> matchToken "+" tokens
    | "-" -> matchToken "-" tokens
    | "*" -> matchToken "*" tokens   
    | "/" -> matchToken "/" tokens               
    | "^" -> matchToken "^" tokens             
    | "<" -> matchToken "<" tokens                 
    | "<=" -> matchToken "<=" tokens                
    | ">" -> matchToken ">" tokens               
    | ">=" -> matchToken ">=" tokens               
    | "==" -> matchToken "==" tokens               
    | "!=" -> matchToken "!=" tokens 
    | _ -> failwith ("expecting expression operator, but found " + nextToken)
  
  and private output tokens = 
    let T2 = matchToken "cout" tokens
    let T3 = matchToken "<<" T2
    let T4 = outputvalue T3
    let T5 = matchToken ";" T4
    T5
  
  and private outputvalue tokens = 
    let nextToken = List.head tokens

    if nextToken = "endl" then
      let T2 = matchToken "endl" tokens
      T2
    else
      let T3 = exprvalue tokens
      T3
  
  and private exprvalue tokens = 
    let nextToken = List.head tokens

    if beginswith "identifier" nextToken then
      let T2 = matchToken "identifier" tokens
      T2
    elif beginswith "int_literal" nextToken then
      let T3 = matchToken "int_literal" tokens
      T3
    elif beginswith "str_literal" nextToken then
      let T4 = matchToken "str_literal" tokens
      T4
    elif nextToken = "true" then
      let T5 = matchToken "true" tokens
      T5
    elif nextToken = "false" then 
      let T6 = matchToken "false" tokens
      T6
    elif beginswith "real_literal" nextToken then
      let T7 = matchToken "real_literal" tokens
      T7
    else
      failwith ("expecting identifier or literal, but found " + nextToken)

  and private input tokens = 
    let T2 = matchToken "cin" tokens
    let T3 = matchToken ">>" T2
    let T4 = matchToken "identifier" T3
    let T5 = matchToken ";" T4
    T5

  and private morestmts tokens =
    let nextToken = List.head tokens
    if nextToken = "}" then
      tokens
    else 
      let T2 = stmt tokens
      morestmts T2

  and private empty tokens = 
    matchToken ";" tokens


  
  //
  // simpleC
  //
  let private simpleC tokens = 
    let T2 = matchToken "void" tokens 
    let T3 = matchToken "main" T2 
    let T4 = matchToken "(" T3 
    let T5 = matchToken ")" T4 
    let T6 = matchToken "{" T5 
    let T7 = stmts T6 // calls recursive descent starting with stmts
    let T8 = matchToken "}" T7 
    let T9 = matchToken "$" T8   // $ => EOF, there should be no more tokens T9
    T9


  //
  // parse tokens
  //
  // Given a list of tokens, parses the list and determines
  // if the list represents a valid SimpleC program.  Returns
  // the string "success" if valid, otherwise returns a 
  // string of the form "syntax_error:...".
  //
  let parse tokens = 
    try
      let result = simpleC tokens
      "Success!"
    with 
      | ex -> "syntax_error: " + ex.Message