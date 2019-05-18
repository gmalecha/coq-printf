Set Primitive Projections.

Variant justify : Set := LeftJustify | RightJustify.

(* Reference : http://www.cplusplus.com/reference/cstdio/printf/            *)
(* %[flags]     [width]  specifier                                          *)
(* %(-|+| |#|0)^* (\d+)    specifier                                        *)
Record options : Set :=
  { option_justify : justify ;  (* '-'   : left justify                     *)
    option_sign : bool ;        (* '+'   : precede with plus sign           *)
    option_space : bool ;       (* ' '   : space if no sign displayed       *)
    option_prefix : bool ;      (* '#'   : precede with o x X , 0 0x 0X     *)
                                (*         for values different than zero   *)
    option_zero_pad : bool ;    (* '0'   : pad with 0's instead of space    *)
    option_width : option nat ; (* (\d+) : width of field                   *)
  }.



(* default options *)
Definition default_options : options :=
  {| option_justify :=  RightJustify ;
     option_sign := false;
     option_space := false;
     option_prefix := false;
     option_zero_pad := false;
     option_width := None;
  |}.

Definition update_option_justify o v :=
  {| option_justify := v ;
     option_sign := o.(option_sign) ;
     option_space := o.(option_space) ;
     option_prefix := o.(option_prefix) ;
     option_zero_pad := o.(option_zero_pad) ;
     option_width := o.(option_width) ;
  |}.

Definition update_option_sign o v :=
  {| option_justify := o.(option_justify) ;
     option_sign := v ;
     option_space := o.(option_space) ;
     option_prefix := o.(option_prefix) ;
     option_zero_pad := o.(option_zero_pad) ;
     option_width := o.(option_width) ;
  |}.

Definition update_option_space o v :=
  {| option_justify := o.(option_justify) ;
     option_sign := o.(option_sign) ;
     option_space := v ;
     option_prefix := o.(option_prefix) ;
     option_zero_pad := o.(option_zero_pad) ;
     option_width := o.(option_width) ;
  |}.

Definition update_option_prefix o v :=
  {| option_justify := o.(option_justify) ;
     option_sign := o.(option_sign) ;
     option_space := o.(option_space) ;
     option_prefix := v ;
     option_zero_pad := o.(option_zero_pad) ;
     option_width := o.(option_width) ;
  |}.

Definition update_option_zero_pad o v :=
  {| option_justify := o.(option_justify) ;
     option_sign := o.(option_sign) ;
     option_space := o.(option_space) ;
     option_prefix := o.(option_prefix) ;
     option_zero_pad := v;
    option_width := option_width o;
  |}.

Definition update_option_width' o width' :=
  {| option_justify := o.(option_justify) ;
     option_sign := o.(option_sign) ;
     option_space := o.(option_space) ;
     option_prefix := o.(option_prefix) ;
     option_zero_pad := o.(option_zero_pad) ;
     option_width := width'
  |}.

Definition update_option_width o width :=
  update_option_width'
    o
    (match option_width o with
     | None => Some width
     | Some width' => Some ((10 * width') + width)
     end).


Theorem option_identity :
  forall o justify sign space prefix zero_pad width ,
         (update_option_width'
         (update_option_zero_pad
         (update_option_prefix
         (update_option_space
         (update_option_sign
         (update_option_justify o justify)
         sign)
         space)
         prefix)
         zero_pad)
         width) =
         {| option_justify := justify ;
            option_sign := sign ;
            option_space := space ;
            option_prefix := prefix ;
            option_zero_pad := zero_pad ;
            option_width := width
         |}.
Proof.
  intros.
  unfold update_option_width'.
  reflexivity.
Qed.
