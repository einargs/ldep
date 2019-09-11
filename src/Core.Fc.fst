module Core.Fc

type file_pos = { row:nat; col:nat }

type file_name = string

type fc =
  | MkFc : file:file_name -> start:file_pos -> stop:file_pos -> fc
  | EmptyFc : fc
