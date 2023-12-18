import os
import itertools
file_path = '/Users/thiamaziz/Desktop/Master 1/RCR/Argumentation/Projet/test_af1.apx'
arguments = []
actions = []
if os.path.exists(file_path):
    try:
        with open(file_path, 'r') as file:
            for line in file:
                stripped_line = line.strip()
                if stripped_line.startswith(("arg(", "att(")):
                    item = stripped_line[4] if stripped_line.startswith("arg(") else stripped_line[4:7:2]
                    (arguments if "arg(" in stripped_line else actions).append(item)
    except Exception as e:
        print(f"An error occurred: {e}")
else:
    print(f"The file {file_path} does not exist.")

print("Les arguments sont :", arguments)
print("Les actions sont :", actions)

def conflict_free(ensemble, actions):
    for i in range(len(ensemble)):
        for j in range(i + 1, len(ensemble)):
            action = ensemble[i] + ensemble[j]
            
            if action in actions or action[::-1] in actions:
                return False
    
    return True


result = conflict_free('CE', actions)
print(result)

def listeAttaque(arguments, actions):
    attaques = {}

    for argument in arguments:
        attaques[argument] = []

    for action in actions:
        attaquant, attaque = action[0], action[1]
        attaques[attaquant].append(attaque)

    return attaques


resultat = listeAttaque(arguments, actions)
print(resultat['A'])


for attaquant, attaques in resultat.items():
    print(f"{attaquant} attaque : {attaques}")


def selfdefense1(elem, arguments, actions):
    try:
        if len(elem) != 1:
            raise ValueError("la taille de l'element est differente de 1")
        
        mla = listeAttaque(arguments, actions)
        for action in actions:
            if elem == action[1] and action[::-1][1] not in mla[elem]:
                return False
        return True
    except ValueError as e:
        print(f"Error: {e}")
        return False

actions = ['AB', 'BC', 'CD']
arguments = ['A', 'B', 'C', 'D']
elem = 'B'

result = selfdefense1(elem, arguments, actions)
print(result)

def selfdefense(elem, arguments, actions):
    mla = listeAttaque(arguments, actions)
    
    for i in range(len(elem)):
        attaquant_defense = elem[i]
        listeDesAttaquesDef = mla[attaquant_defense].copy()
        listeDesAttaquesAtt = []  # Initialize the list
        
        for action in actions:
            attaquant = action[0]
            defenseur = action[1]
            
            if attaquant_defense == defenseur:
                listeDesAttaquesDef = mla[defenseur].copy()
                
                if attaquant in listeDesAttaquesDef:  
                    listeDesAttaquesAtt = list(mla[attaquant])
                    if defenseur in listeDesAttaquesAtt:
                        listeDesAttaquesAtt.remove(defenseur)
                
                if attaquant not in listeDesAttaquesDef: 
                    for j in range(len(elem)):
                        if j != i and attaquant in mla[elem[j]]:
                            if defenseur in listeDesAttaquesAtt:
                                listeDesAttaquesAtt.remove(defenseur)
                                
        if attaquant_defense not in listeDesAttaquesAtt:
            continue
        else:
            return False
   
            
            
            
        



