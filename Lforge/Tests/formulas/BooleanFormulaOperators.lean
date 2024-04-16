import Lforge

pred p_True {
    univ = univ
}

pred p_False {
    univ != univ
}

pred p_Not { -- !, not
    !(!True)
    !False

    not (not True)
    not False
}

pred p_And { -- &&, and
    True && True
    not (True && False)
    not (False && True)
    not (False && False)

    True and True
    not (True and False)
    not (False and True)
    not (False and False)
}

pred p_Or { -- ||, or
    True || True
    True || False
    False || True
    not (False || False)

    True or True
    True or False
    False or True
    not (False or False)
}

pred p_Implies { -- =>, implies, <=>, iff, => else, implies else
    True => True
    not (True => False)
    False => True
    False => False

    True implies True
    not (True implies False)
    False implies True
    False implies False

    True <=> True
    not (True <=> False)
    not (False <=> True)
    False <=> False

    True iff True
    not (True iff False)
    not (False iff True)
    False iff False

    True => True else True
    True => True else False
    not (True => False else True)
    not (True => False else False)
    False => True else True
    not (False => True else False)
    False => False else True
    not (False => False else False)

    True implies True else True
    True implies True else False
    not (True implies False else True)
    not (True implies False else False)
    False implies True else True
    not (False implies True else False)
    False implies False else True
    not (False implies False else False)
}
