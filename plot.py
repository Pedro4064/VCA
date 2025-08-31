import pandas as pd
import matplotlib.pyplot as plt

# Replace with your CSV file name
filename = "data"

# Read CSV with no header (3 values per row)
df = pd.read_csv(filename, header=None, names=["y", "yd", "ydd", "y_filtered", "t"])

# Plot
plt.figure(figsize=(10, 6))
plt.plot(df["t"],df["y"], label="y")
plt.plot(df["t"],df["yd"], label="yd")
plt.plot(df["t"],df["y_filtered"], label="y_filtered")

plt.xlabel("Sample Index")
plt.ylabel("Value")
plt.title("y, yd, ydd from CSV")
plt.legend()
plt.grid(True)
plt.show()
