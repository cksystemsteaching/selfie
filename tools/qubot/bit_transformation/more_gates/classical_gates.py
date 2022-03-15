def l_NOT(x1):
    return not x1

def l_NAND(x1, x2):
    return not (x1 and x2)

def l_AND(x1, x2):
    return x1 and x2

def l_XOR(x1, x2):
    return x1 != x2
    
def l_XNOR(x1, x2):
    return x1 == x2