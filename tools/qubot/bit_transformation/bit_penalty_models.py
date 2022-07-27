from typing import List, Dict, Any

import penaltymodel.core as pm
import dimod
import networkx as nx
from bit_transformation.configurations import *
import itertools


class Models:
    models: Dict[Config, Any] = {}
    energies: Dict[Config, Any] = {}
    preloaded_configs: List[Config] = [Config.MATRIARCH1, Config.AND, Config.NAND, Config.OR, Config.NOT, Config.XOR]

    @staticmethod
    def get_model(config: Config):
        if config not in Models.models.keys():
            if config != Config.XNOR:
                if config in Models.preloaded_configs:
                    if config == Config.AND:
                        linear = {'x1':0,'x2':0, 'z':6}
                        quadratic = {('x1','x2'): 2, ('x1','z'):-4,('x2','z'):-4}
                        offset = 0
                    elif config == Config.NAND:
                        linear = {'x1': -4, 'x2': -4, 'z': -6}
                        quadratic = {('x1', 'x2'): 2, ('x1', 'z'): 4, ('x2', 'z'): 4}
                        offset = 6
                    elif config == Config.MATRIARCH1:
                        linear = {'x1': 0, 'x2': 2, 'z': 2}
                        quadratic = {('x1', 'x2'): -2, ('x1', 'z'): 4, ('x2', 'z'): -4}
                        offset = 0
                    elif config == Config.OR:
                        linear = {'x1': 2, 'x2': 2, 'z': 2}
                        quadratic = {('x1', 'x2'): 2, ('x1', 'z'): -4, ('x2', 'z'): -4}
                        offset = 0
                    elif config == Config.NOT:
                        linear = {'x1': -2, 'x2':-2}
                        quadratic = {('x1', 'x2'): 4}
                        offset = 2
                    elif config == Config.XOR:
                        linear = {'x1': 1, 'x2': 1, 'z': 1, 'a': 4}
                        quadratic = {('x1', 'x2'): 2, ('x1', 'z'): -2, ('x2', 'z'): -2,('x1', 'a'): -4,
                                     ('x2', 'a'): -4, ('a', 'z'): 4}
                    else:
                        raise Exception("Strange Error. Tried to return prebuilded model, but this model does not exists.")


                    result = dimod.BinaryQuadraticModel(linear, quadratic,offset, dimod.BINARY)
                    Models.models[config] = result
                    return result
                else:
                    feasable_configs, _ = get_config(config)
                    graph = nx.Graph()

                    if config != Config.NOT:
                        decision_variables = ["x1", "x2", "z"]
                        graph.add_edges_from([("x1", "x2"), ("x1", "z"), ("x2", "z")])
                    else:
                        decision_variables = ["x1", "x2"]
                        graph.add_edges_from([("x1", "x2")])

                    spec = pm.Specification(graph, decision_variables, feasable_configs, dimod.BINARY)
                    p_model = pm.get_penalty_model(
                        spec)  # https://github.com/dwavesystems/penaltymodel/blob/master/penaltymodel_core/penaltymodel/core/classes/penaltymodel.py
                    # p_model.model --> https://test-projecttemplate-dimod.readthedocs.io/en/latest/reference/bqm/binary_quadratic_model.html#dimod.BinaryQuadraticModel
                    # ground_energy = p_model.ground_energy
                    Models.models[config] = p_model.model
            else:
                raise Exception(
                    "For XOR and XNOR run bit_transformation/more_gates/xor.py or bit_transformation/more_gates/xnor.py")
        return Models.models[config]

def get_model(config: Config, decision_variables: List[int]) -> (dimod.BinaryQuadraticModel, float):
    '''

    :param config: gate to use
    :param decision_variables: list of names [x1,x2,z] to assign to the qubits for a gate with inputs x1, x2 and
    output z.
    :return:
    '''
    model = Models.get_model(config)
    model = model.copy()
    if config == Config.NOT:
        model.relabel_variables({'x1': decision_variables[0], 'x2': decision_variables[1]})
    else:
        model.relabel_variables({'x1': decision_variables[0], 'x2': decision_variables[1], 'z': decision_variables[2]})
    return model, None




def run_model(config: Config):
    # sampler = dimod.ExactSolver() # runs using classical resources. We can use this to test that a given BQM is correct
    _, name = get_config(config)
    if config != Config.NOT:
        decision_variables = ['x1', 'x2', 'z']
    else:
        decision_variables = ['x1', 'nx1']
    model, ground_energy = get_model(config, decision_variables)

    f = open("./results/" + name + ".csv", "w")

    f.write(f'x1,x2,z, E (G={str(ground_energy)})\n')

    if config != Config.NOT:
        for (x1, x2, z) in list(itertools.product([0, 1], repeat=len(decision_variables))):
            current_energy = model.energy({'x1': x1, 'x2': x2, 'z': z})
            f.write(f'{x1},{x2},{z},{round(current_energy, 2)}\n')
    else:
        for (x1, x2) in list(itertools.product([0, 1], repeat=len(decision_variables))):
            current_energy = model.energy({'x1': x1, 'nx1': x2})
            f.write(f'{x1},{x2},{round(current_energy, 2)}\n')
    return True


if __name__ == '__main__':
    for c in Config:
        try:
            run_model(c)
        except:
            print(f'No model found for {c}')
