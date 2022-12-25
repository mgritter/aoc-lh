import matplotlib.pyplot as plt
import numpy as np

reachable = set()

maxZ = 200

# voxel array
a = np.zeros((100, 38, maxZ + 1))            

for z in range( maxZ + 1 ):
    reachable.add( (z,1,0) )
    a[1,0,z] = 1
    
fig = plt.figure(figsize=(9, 6))
# Create 3D container
ax = plt.axes(projection = '3d', azim=60)

with open( "coords.txt", "r") as inFile:
    for line in inFile:
        toks = line.split( "," )
        z = int( toks[0] )
        x = int( toks[1] )
        y = int( toks[2] )
        if z > maxZ:
            break
            
        if (z-1,x-1,y) in reachable or \
           (z-1,x+1,y) in reachable or \
           (z-1,x,y-1) in reachable or \
           (z-1,x,y+1) in reachable or \
           (z-1,x,y) in reachable:
            reachable.add( (z,x,y) )            
            a[x,y,z] = 1



# Visualize 3D scatter plot
ax.voxels(filled=a )
# Give labels
ax.set_xlabel('x')
ax.set_ylabel('y')
ax.set_zlabel('time')

# Save figure
plt.savefig('3d_scatter.png', dpi = 300);    
