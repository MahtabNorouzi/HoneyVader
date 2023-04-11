import matplotlib.pyplot as plt

if __name__ == "__main__":
# Define the data
    uot_bytecode = 5034
    uot_source = 3027
    fc_bytecode = 46
    fo_bytecode = 23
    hp_bytecode = 69
    fc_source = 44
    fo_source = 12
    hp_source = 56

    # Set up the plot
    fig, axs = plt.subplots(1, 4, figsize=(10, 4))
    fig.suptitle('Number of Source Code and Byte Code for Honeypots', fontsize=14, fontweight='bold')

    # UOT plot
    axs[0].bar(['Bytecode', 'Source Code'], [uot_bytecode, uot_source], color=['#1f77b4', '#ff7f0e'])
    axs[0].set_title('UOT', fontweight='bold')
    axs[0].set_ylabel('Values')
    axs[0].set_ylim([0, max(uot_bytecode, uot_source) + 10])

    # FC plot
    axs[1].bar(['Bytecode', 'Source Code'], [fc_bytecode, fc_source], color=['#1f77b4', '#ff7f0e'])
    axs[1].set_title('FC', fontweight='bold')
    axs[1].set_ylim([0, max(fc_bytecode, fc_source) + 10])

    # FO plot
    axs[2].bar(['Bytecode', 'Source Code'], [fo_bytecode, fo_source], color=['#1f77b4', '#ff7f0e'])
    axs[2].set_title('FO', fontweight='bold')
    axs[2].set_ylim([0, max(fo_bytecode, fo_source) + 10])

    # HP plot
    axs[3].bar(['Bytecode', 'Source Code'], [hp_bytecode, hp_source], color=['#1f77b4', '#ff7f0e'])
    axs[3].set_title('HP', fontweight='bold')
    axs[3].set_ylim([0, max(hp_bytecode, hp_source) + 10])

    # Add vertical lines to separate the charts
    for ax in axs:
        ax.axvline(x=0.5, color='gray', linestyle='--')

    # Save the figure
    # plt.savefig('chart.png', dpi=300, bbox_inches='tight')
    plt.show()