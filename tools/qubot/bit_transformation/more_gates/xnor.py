import itertools
from typing import Dict

from bit_transformation.more_gates.classical_gates import *
from dimod import ExactSolver
from bit_transformation.bit_penalty_models import get_model
from bit_transformation.configurations import Config


def test_circuit():
    for (x1, x2) in list(itertools.product([0, 1], repeat=2)):
        n_x1 = l_NOT(x1)
        n_x2 = l_NOT(x2)
        result = l_NAND(l_NAND(x1,x2), l_NAND(n_x1,n_x2))
        assert(result == l_XNOR(x1,x2))


def get_XNOR(var_names: Dict[str, int] = None):

    if var_names is None:
        var_names = {
            'x1': 0,
            'x2': 1,
            'nx1': 2,
            'nx2': 3,
            'nand1': 4,
            'nand2': 5,
            'z': 6
        }
    if var_names['x1'] == var_names['x2']:
        model, _ = get_model(Config.NOT, [var_names['x1'], var_names['nx1']])
        model.update(get_model(Config.NAND, [var_names['x1'], var_names['nx1'], var_names['z']])[0])
    else:
        model, _ = get_model(Config.NOT, [var_names['x1'], var_names['nx1']])
        model.update(get_model(Config.NOT, [var_names['x2'], var_names['nx2']])[0])
        model.update(get_model(Config.NAND, [var_names['x1'], var_names['x2'], var_names['nand1']])[0])
        model.update(get_model(Config.NAND, [var_names['nx1'], var_names['nx2'], var_names['nand2']])[0])
        model.update(get_model(Config.NAND, [var_names['nand1'], var_names['nand2'], var_names['z']])[0])
    return model

def test_quantum_circuit():
    f = open("./results/XNOR.csv", "w")
    f.write(f'x1,x2,~x1,~x2,NAND(x1-x2),NAND(~x1-~x2),z,E\n')

    for (x1, x2) in list(itertools.product([0, 1], repeat=2)):
        model = get_XNOR()
        model.fix_variable('x1', x1)
        model.fix_variable('x2', x2)
        sampler = ExactSolver()
        result = sampler.sample(model).first
        vars = result[0]
        energy = result.energy
        f.write(f"{x1},{x2},{vars['nx1']},{vars['nx2']},{vars['nand1']}, {vars['nand2']},{vars['z']},{round(energy,2)}\n")
        assert(l_NOT(x1) == vars['nx1'])
        assert(l_NOT(x2) == vars['nx2'])
        assert(l_NAND(x1,x2) == vars['nand1'])
        assert(l_NAND(l_NOT(x1),l_NOT(x2)) == vars['nand2'])
        assert(l_XNOR(x1,x2) == vars['z'])
        

if __name__ == '__main__':
    test_circuit()
    test_quantum_circuit()
